open Prims
type printing_mode =
  | ToTempFile 
  | FromTempToStdout 
  | FromTempToFile 
let uu___is_ToTempFile (projectee : printing_mode) : Prims.bool=
  match projectee with | ToTempFile -> true | uu___ -> false
let uu___is_FromTempToStdout (projectee : printing_mode) : Prims.bool=
  match projectee with | FromTempToStdout -> true | uu___ -> false
let uu___is_FromTempToFile (projectee : printing_mode) : Prims.bool=
  match projectee with | FromTempToFile -> true | uu___ -> false
let temp_file_name (f : Prims.string) : Prims.string=
  FStarC_Format.fmt1 "%s.print_.fst" f
let generate (m : printing_mode) (filenames : Prims.string Prims.list) :
  unit=
  let parse_and_prettyprint m1 filename =
    let uu___ = FStarC_Parser_Driver.parse_file filename in
    match uu___ with
    | (modul, comments) ->
        let outf =
          match m1 with
          | FromTempToStdout -> FStar_Pervasives_Native.None
          | FromTempToFile ->
              let outf1 = FStarC_Util.open_file_for_writing filename in
              FStar_Pervasives_Native.Some outf1
          | ToTempFile ->
              let outf1 =
                let uu___1 = temp_file_name filename in
                FStarC_Util.open_file_for_writing uu___1 in
              FStar_Pervasives_Native.Some outf1 in
        let leftover_comments =
          let comments1 = FStarC_List.rev comments in
          let uu___1 =
            FStarC_Parser_ToDocument.modul_with_comments_to_document modul
              comments1 in
          match uu___1 with
          | (doc, comments2) ->
              ((match outf with
                | FStar_Pervasives_Native.Some f ->
                    let uu___3 =
                      FStarC_Pprint.pretty_string
                        (FStarC_Util.float_of_string "1.0")
                        (Prims.of_int (100)) doc in
                    FStarC_Util.append_to_file f uu___3
                | FStar_Pervasives_Native.None ->
                    FStarC_Pprint.pretty_out_channel
                      (FStarC_Util.float_of_string "1.0")
                      (Prims.of_int (100)) doc FStarC_Util.stdout);
               comments2) in
        let left_over_doc =
          if Prims.op_Negation (FStarC_List.isEmpty leftover_comments)
          then
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    FStarC_Parser_ToDocument.comments_to_document
                      leftover_comments in
                  [uu___4] in
                FStar_Pprint.hardline :: uu___3 in
              FStar_Pprint.hardline :: uu___2 in
            FStar_Pprint.concat uu___1
          else
            if m1 = FromTempToStdout
            then
              FStar_Pprint.concat
                [FStar_Pprint.hardline; FStar_Pprint.hardline]
            else FStar_Pprint.empty in
        (match outf with
         | FStar_Pervasives_Native.None ->
             FStarC_Pprint.pretty_out_channel
               (FStarC_Util.float_of_string "1.0") (Prims.of_int (100))
               left_over_doc FStarC_Util.stdout
         | FStar_Pervasives_Native.Some outf1 ->
             ((let uu___2 =
                 FStarC_Pprint.pretty_string
                   (FStarC_Util.float_of_string "1.0") (Prims.of_int (100))
                   left_over_doc in
               FStarC_Util.append_to_file outf1 uu___2);
              FStarC_Util.close_out_channel outf1)) in
  FStarC_List.iter (parse_and_prettyprint m) filenames
