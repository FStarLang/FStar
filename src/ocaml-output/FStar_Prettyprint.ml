open Prims
type printing_mode =
  | ToTempFile 
  | FromTempToStdout 
  | FromTempToFile 
let (uu___is_ToTempFile : printing_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | ToTempFile  -> true | uu____47485 -> false
  
let (uu___is_FromTempToStdout : printing_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | FromTempToStdout  -> true | uu____47496 -> false
  
let (uu___is_FromTempToFile : printing_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | FromTempToFile  -> true | uu____47507 -> false
  
let (temp_file_name : Prims.string -> Prims.string) =
  fun f  -> FStar_Util.format1 "%s.print_.fst" f 
let (generate : printing_mode -> Prims.string Prims.list -> unit) =
  fun m  ->
    fun filenames  ->
      let parse_and_prettyprint m1 filename =
        let uu____47549 =
          match m1 with
          | ToTempFile  ->
              let uu____47564 =
                let uu____47567 =
                  let uu____47568 = temp_file_name filename  in
                  FStar_Util.open_file_for_writing uu____47568  in
                FStar_Pervasives_Native.Some uu____47567  in
              (filename, uu____47564)
          | FromTempToFile  ->
              let uu____47573 = temp_file_name filename  in
              let uu____47575 =
                let uu____47578 = FStar_Util.open_file_for_writing filename
                   in
                FStar_Pervasives_Native.Some uu____47578  in
              (uu____47573, uu____47575)
          | FromTempToStdout  ->
              let uu____47582 = temp_file_name filename  in
              (uu____47582, FStar_Pervasives_Native.None)
           in
        match uu____47549 with
        | (inf,outf) ->
            let uu____47595 = FStar_Parser_Driver.parse_file inf  in
            (match uu____47595 with
             | (modul,comments) ->
                 let leftover_comments =
                   let comments1 = FStar_List.rev comments  in
                   let uu____47644 =
                     FStar_Parser_ToDocument.modul_with_comments_to_document
                       modul comments1
                      in
                   match uu____47644 with
                   | (doc1,comments2) ->
                       ((match outf with
                         | FStar_Pervasives_Native.Some f ->
                             let uu____47681 =
                               FStar_Pprint.pretty_string
                                 (FStar_Util.float_of_string "1.0")
                                 (Prims.parse_int "100") doc1
                                in
                             FStar_All.pipe_left
                               (FStar_Util.append_to_file f) uu____47681
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
                     let uu____47695 =
                       let uu____47698 =
                         let uu____47701 =
                           let uu____47704 =
                             FStar_Parser_ToDocument.comments_to_document
                               leftover_comments
                              in
                           [uu____47704]  in
                         FStar_Pprint.hardline :: uu____47701  in
                       FStar_Pprint.hardline :: uu____47698  in
                     FStar_Pprint.concat uu____47695
                   else
                     if m1 = FromTempToStdout
                     then
                       FStar_Pprint.concat
                         [FStar_Pprint.hardline; FStar_Pprint.hardline]
                     else FStar_Pprint.empty
                    in
                 (match outf with
                  | FStar_Pervasives_Native.Some f ->
                      ((let uu____47712 =
                          FStar_Pprint.pretty_string
                            (FStar_Util.float_of_string "1.0")
                            (Prims.parse_int "100") left_over_doc
                           in
                        FStar_All.pipe_left (FStar_Util.append_to_file f)
                          uu____47712);
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
                let uu____47726 = temp_file_name f  in
                FStar_Util.delete_file uu____47726) filenames
       | FromTempToStdout  ->
           FStar_List.iter
             (fun f  ->
                let uu____47733 = temp_file_name f  in
                FStar_Util.delete_file uu____47733) filenames
       | ToTempFile  -> ())
  