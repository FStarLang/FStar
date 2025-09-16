open Prims
type error_message = FStar_Pprint.document Prims.list
type 't is_error_message = {
  to_doc_list: 't -> error_message }
let __proj__Mkis_error_message__item__to_doc_list :
  't . 't is_error_message -> 't -> error_message =
  fun projectee -> match projectee with | { to_doc_list;_} -> to_doc_list
let to_doc_list : 't . 't is_error_message -> 't -> error_message =
  fun projectee ->
    match projectee with | { to_doc_list = to_doc_list1;_} -> to_doc_list1
let (is_error_message_string : Prims.string is_error_message) =
  { to_doc_list = (fun s -> [FStar_Pprint.arbitrary_string s]) }
let (is_error_message_list_doc :
  FStar_Pprint.document Prims.list is_error_message) =
  { to_doc_list = (fun x -> x) }
let (vconcat : FStar_Pprint.document Prims.list -> FStar_Pprint.document) =
  fun ds ->
    match ds with
    | h::t ->
        FStarC_List.fold_left
          (fun l ->
             fun r ->
               FStar_Pprint.op_Hat_Hat l
                 (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline r)) h t
    | [] -> FStar_Pprint.empty
let (text : Prims.string -> FStar_Pprint.document) =
  fun s ->
    FStar_Pprint.flow (FStar_Pprint.break_ Prims.int_one)
      (FStar_Pprint.words s)
let (sublist :
  FStar_Pprint.document ->
    FStar_Pprint.document Prims.list -> FStar_Pprint.document)
  =
  fun h ->
    fun ds ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              FStarC_List.map (fun d -> FStar_Pprint.op_Hat_Hat h d) ds in
            vconcat uu___3 in
          FStar_Pprint.align uu___2 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___1 in
      FStar_Pprint.nest (Prims.of_int (2)) uu___
let (bulleted : FStar_Pprint.document Prims.list -> FStar_Pprint.document) =
  fun ds -> sublist (FStar_Pprint.doc_of_string "- ") ds
let (mkmsg : Prims.string -> error_message) =
  fun s -> [FStar_Pprint.arbitrary_string s]
let (renderdoc : FStar_Pprint.document -> Prims.string) =
  fun d ->
    let one = FStarC_Util.float_of_string "1.0" in
    FStarC_Pprint.pretty_string one (Prims.of_int (80)) d
let (backtrace_doc : unit -> FStar_Pprint.document) =
  fun uu___ ->
    let s = FStarC_Util.stack_dump () in
    let uu___1 = text "Stack trace:" in
    FStar_Pprint.op_Hat_Slash_Hat uu___1
      (FStar_Pprint.arbitrary_string (FStarC_Util.trim_string s))
let (subdoc' : Prims.bool -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun indent ->
    fun d ->
      if d = FStar_Pprint.empty
      then FStar_Pprint.empty
      else
        FStar_Pprint.op_Hat_Hat
          (if indent
           then FStar_Pprint.blank (Prims.of_int (2))
           else FStar_Pprint.empty)
          (FStar_Pprint.op_Hat_Hat (FStar_Pprint.doc_of_string "-")
             (FStar_Pprint.op_Hat_Hat (FStar_Pprint.blank Prims.int_one)
                (FStar_Pprint.op_Hat_Hat (FStar_Pprint.align d)
                   FStar_Pprint.hardline)))
let (subdoc : FStar_Pprint.document -> FStar_Pprint.document) =
  fun d -> subdoc' true d
let (render_as_doc :
  FStar_Pprint.document Prims.list -> FStar_Pprint.document) =
  fun ds ->
    let uu___ = FStarC_List.map (fun d -> subdoc (FStar_Pprint.group d)) ds in
    FStar_Pprint.concat uu___
let (rendermsg : error_message -> Prims.string) =
  fun ds -> let uu___ = render_as_doc ds in renderdoc uu___
let (json_of_error_message :
  FStar_Pprint.document Prims.list -> FStarC_Json.json) =
  fun err_msg ->
    let uu___ =
      FStarC_List.map
        (fun doc -> let uu___1 = renderdoc doc in FStarC_Json.JsonStr uu___1)
        err_msg in
    FStarC_Json.JsonList uu___
