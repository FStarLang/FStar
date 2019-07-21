open Prims
type printing_mode =
  | ToTempFile 
  | FromTempToStdout 
  | FromTempToFile 
let (uu___is_ToTempFile : printing_mode -> Prims.bool) =
  fun projectee ->
    match projectee with | ToTempFile -> true | uu____8 -> false
let (uu___is_FromTempToStdout : printing_mode -> Prims.bool) =
  fun projectee ->
    match projectee with | FromTempToStdout -> true | uu____19 -> false
let (uu___is_FromTempToFile : printing_mode -> Prims.bool) =
  fun projectee ->
    match projectee with | FromTempToFile -> true | uu____30 -> false
let (temp_file_name : Prims.string -> Prims.string) =
  fun f -> FStar_Util.format1 "%s.print_.fst" f
let (generate : printing_mode -> Prims.string Prims.list -> unit) =
  fun m ->
    fun filenames ->
      let parse_and_prettyprint m1 filename =
        let uu____72 =
          match m1 with
          | ToTempFile ->
              let uu____87 =
                let uu____90 =
                  let uu____91 = temp_file_name filename in
                  FStar_Util.open_file_for_writing uu____91 in
                FStar_Pervasives_Native.Some uu____90 in
              (filename, uu____87)
          | FromTempToFile ->
              let uu____96 = temp_file_name filename in
              let uu____98 =
                let uu____101 = FStar_Util.open_file_for_writing filename in
                FStar_Pervasives_Native.Some uu____101 in
              (uu____96, uu____98)
          | FromTempToStdout ->
              let uu____105 = temp_file_name filename in
              (uu____105, FStar_Pervasives_Native.None) in
        match uu____72 with
        | (inf, outf) ->
            let uu____118 = FStar_Parser_Driver.parse_file inf in
            (match uu____118 with
             | (modul, comments) ->
                 let leftover_comments =
                   let comments1 = FStar_List.rev comments in
                   let uu____167 =
                     FStar_Parser_ToDocument.modul_with_comments_to_document
                       modul comments1 in
                   match uu____167 with
                   | (doc1, comments2) ->
                       ((match outf with
                         | FStar_Pervasives_Native.Some f ->
                             let uu____204 =
                               FStar_Pprint.pretty_string
                                 (FStar_Util.float_of_string "1.0")
                                 (Prims.parse_int "100") doc1 in
                             FStar_All.pipe_left
                               (FStar_Util.append_to_file f) uu____204
                         | FStar_Pervasives_Native.None ->
                             FStar_Pprint.pretty_out_channel
                               (FStar_Util.float_of_string "1.0")
                               (Prims.parse_int "100") doc1 FStar_Util.stdout);
                        comments2) in
                 let left_over_doc =
                   if
                     Prims.op_Negation (FStar_List.isEmpty leftover_comments)
                   then
                     let uu____218 =
                       let uu____221 =
                         let uu____224 =
                           let uu____227 =
                             FStar_Parser_ToDocument.comments_to_document
                               leftover_comments in
                           [uu____227] in
                         FStar_Pprint.hardline :: uu____224 in
                       FStar_Pprint.hardline :: uu____221 in
                     FStar_Pprint.concat uu____218
                   else
                     if m1 = FromTempToStdout
                     then
                       FStar_Pprint.concat
                         [FStar_Pprint.hardline; FStar_Pprint.hardline]
                     else FStar_Pprint.empty in
                 (match outf with
                  | FStar_Pervasives_Native.Some f ->
                      ((let uu____235 =
                          FStar_Pprint.pretty_string
                            (FStar_Util.float_of_string "1.0")
                            (Prims.parse_int "100") left_over_doc in
                        FStar_All.pipe_left (FStar_Util.append_to_file f)
                          uu____235);
                       FStar_Util.close_file f)
                  | FStar_Pervasives_Native.None ->
                      FStar_Pprint.pretty_out_channel
                        (FStar_Util.float_of_string "1.0")
                        (Prims.parse_int "100") left_over_doc
                        FStar_Util.stdout)) in
      FStar_List.iter (parse_and_prettyprint m) filenames;
      (match m with
       | FromTempToFile ->
           FStar_List.iter
             (fun f ->
                let uu____249 = temp_file_name f in
                FStar_Util.delete_file uu____249) filenames
       | FromTempToStdout ->
           FStar_List.iter
             (fun f ->
                let uu____256 = temp_file_name f in
                FStar_Util.delete_file uu____256) filenames
       | ToTempFile -> ())