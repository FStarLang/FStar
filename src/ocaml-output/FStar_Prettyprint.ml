open Prims
type printing_mode =
  | ToTempFile 
  | FromTempToStdout 
  | FromTempToFile 
let (uu___is_ToTempFile : printing_mode -> Prims.bool) =
  fun projectee ->
    match projectee with | ToTempFile -> true | uu____5 -> false
let (uu___is_FromTempToStdout : printing_mode -> Prims.bool) =
  fun projectee ->
    match projectee with | FromTempToStdout -> true | uu____11 -> false
let (uu___is_FromTempToFile : printing_mode -> Prims.bool) =
  fun projectee ->
    match projectee with | FromTempToFile -> true | uu____17 -> false
let (temp_file_name : Prims.string -> Prims.string) =
  fun f -> FStar_Util.format1 "%s.print_.fst" f
let (generate : printing_mode -> Prims.string Prims.list -> unit) =
  fun m ->
    fun filenames ->
      let parse_and_prettyprint m1 filename =
        let uu____48 = FStar_Parser_Driver.parse_file filename in
        match uu____48 with
        | (modul, comments) ->
            let outf =
              match m1 with
              | FromTempToStdout -> FStar_Pervasives_Native.None
              | FromTempToFile ->
                  let outf = FStar_Util.open_file_for_writing filename in
                  FStar_Pervasives_Native.Some outf
              | ToTempFile ->
                  let outf =
                    let uu____80 = temp_file_name filename in
                    FStar_Util.open_file_for_writing uu____80 in
                  FStar_Pervasives_Native.Some outf in
            let leftover_comments =
              let comments1 = FStar_List.rev comments in
              let uu____99 =
                FStar_Parser_ToDocument.modul_with_comments_to_document modul
                  comments1 in
              match uu____99 with
              | (doc, comments2) ->
                  ((match outf with
                    | FStar_Pervasives_Native.Some f ->
                        let uu____132 =
                          FStar_Pprint.pretty_string
                            (FStar_Util.float_of_string "1.0")
                            (Prims.of_int (100)) doc in
                        FStar_All.pipe_left (FStar_Util.append_to_file f)
                          uu____132
                    | FStar_Pervasives_Native.None ->
                        FStar_Pprint.pretty_out_channel
                          (FStar_Util.float_of_string "1.0")
                          (Prims.of_int (100)) doc FStar_Util.stdout);
                   comments2) in
            let left_over_doc =
              if Prims.op_Negation (FStar_List.isEmpty leftover_comments)
              then
                let uu____138 =
                  let uu____141 =
                    let uu____144 =
                      let uu____147 =
                        FStar_Parser_ToDocument.comments_to_document
                          leftover_comments in
                      [uu____147] in
                    FStar_Pprint.hardline :: uu____144 in
                  FStar_Pprint.hardline :: uu____141 in
                FStar_Pprint.concat uu____138
              else
                if m1 = FromTempToStdout
                then
                  FStar_Pprint.concat
                    [FStar_Pprint.hardline; FStar_Pprint.hardline]
                else FStar_Pprint.empty in
            (match outf with
             | FStar_Pervasives_Native.None ->
                 FStar_Pprint.pretty_out_channel
                   (FStar_Util.float_of_string "1.0") (Prims.of_int (100))
                   left_over_doc FStar_Util.stdout
             | FStar_Pervasives_Native.Some outf1 ->
                 ((let uu____152 =
                     FStar_Pprint.pretty_string
                       (FStar_Util.float_of_string "1.0")
                       (Prims.of_int (100)) left_over_doc in
                   FStar_All.pipe_left (FStar_Util.append_to_file outf1)
                     uu____152);
                  FStar_Util.close_file outf1)) in
      FStar_List.iter (parse_and_prettyprint m) filenames