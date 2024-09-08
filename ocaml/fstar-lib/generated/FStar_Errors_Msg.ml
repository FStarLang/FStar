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
  {
    to_doc_list =
      (fun s -> let uu___ = FStar_Pprint.arbitrary_string s in [uu___])
  }
let (is_error_message_list_doc :
  FStar_Pprint.document Prims.list is_error_message) =
  { to_doc_list = (fun x -> x) }
let (vconcat : FStar_Pprint.document Prims.list -> FStar_Pprint.document) =
  fun ds ->
    match ds with
    | h::t ->
        FStar_Compiler_List.fold_left
          (fun l ->
             fun r ->
               let uu___ = FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline r in
               FStar_Pprint.op_Hat_Hat l uu___) h t
    | [] -> FStar_Pprint.empty
let (text : Prims.string -> FStar_Pprint.document) =
  fun s ->
    let uu___ = FStar_Pprint.break_ Prims.int_one in
    let uu___1 = FStar_Pprint.words s in FStar_Pprint.flow uu___ uu___1
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
              FStar_Compiler_List.map (fun d -> FStar_Pprint.op_Hat_Hat h d)
                ds in
            vconcat uu___3 in
          FStar_Pprint.align uu___2 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___1 in
      FStar_Pprint.nest (Prims.of_int (2)) uu___
let (bulleted : FStar_Pprint.document Prims.list -> FStar_Pprint.document) =
  fun ds -> let uu___ = FStar_Pprint.doc_of_string "- " in sublist uu___ ds
let (mkmsg : Prims.string -> error_message) =
  fun s -> let uu___ = FStar_Pprint.arbitrary_string s in [uu___]
let (renderdoc : FStar_Pprint.document -> Prims.string) =
  fun d ->
    let one = FStar_Compiler_Util.float_of_string "1.0" in
    FStar_Pprint.pretty_string one (Prims.of_int (80)) d
let (backtrace_doc : unit -> FStar_Pprint.document) =
  fun uu___ ->
    let s = FStar_Compiler_Util.stack_dump () in
    let uu___1 = text "Stack trace:" in
    let uu___2 =
      FStar_Pprint.arbitrary_string (FStar_Compiler_Util.trim_string s) in
    FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2
let (subdoc' : Prims.bool -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun indent ->
    fun d ->
      if d = FStar_Pprint.empty
      then FStar_Pprint.empty
      else
        (let uu___1 =
           if indent
           then FStar_Pprint.blank (Prims.of_int (2))
           else FStar_Pprint.empty in
         let uu___2 =
           let uu___3 = FStar_Pprint.doc_of_string "-" in
           let uu___4 =
             let uu___5 = FStar_Pprint.blank Prims.int_one in
             let uu___6 =
               let uu___7 = FStar_Pprint.align d in
               FStar_Pprint.op_Hat_Hat uu___7 FStar_Pprint.hardline in
             FStar_Pprint.op_Hat_Hat uu___5 uu___6 in
           FStar_Pprint.op_Hat_Hat uu___3 uu___4 in
         FStar_Pprint.op_Hat_Hat uu___1 uu___2)
let (subdoc : FStar_Pprint.document -> FStar_Pprint.document) =
  fun d -> subdoc' true d
let (rendermsg : error_message -> Prims.string) =
  fun ds ->
    let uu___ =
      let uu___1 =
        FStar_Compiler_List.map
          (fun d -> let uu___2 = FStar_Pprint.group d in subdoc uu___2) ds in
      FStar_Pprint.concat uu___1 in
    renderdoc uu___