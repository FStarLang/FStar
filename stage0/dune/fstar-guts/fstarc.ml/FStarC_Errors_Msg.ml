open Prims
type error_message = FStar_Pprint.document Prims.list
type 't is_error_message = {
  to_doc_list: 't -> error_message }
let __proj__Mkis_error_message__item__to_doc_list
  (projectee : 't is_error_message) : 't -> error_message=
  match projectee with | { to_doc_list;_} -> to_doc_list
let to_doc_list (projectee : 't is_error_message) : 't -> error_message=
  match projectee with | { to_doc_list = to_doc_list1;_} -> to_doc_list1
let is_error_message_string : Prims.string is_error_message=
  { to_doc_list = (fun s -> [FStar_Pprint.arbitrary_string s]) }
let is_error_message_list_doc :
  FStar_Pprint.document Prims.list is_error_message=
  { to_doc_list = (fun x -> x) }
let vconcat (ds : FStar_Pprint.document Prims.list) : FStar_Pprint.document=
  match ds with
  | h::t ->
      FStarC_List.fold_left
        (fun l r ->
           FStar_Pprint.op_Hat_Hat l
             (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline r)) h t
  | [] -> FStar_Pprint.empty
let text (s : Prims.string) : FStar_Pprint.document=
  FStar_Pprint.flow (FStar_Pprint.break_ Prims.int_one)
    (FStar_Pprint.words s)
let sublist (h : FStar_Pprint.document)
  (ds : FStar_Pprint.document Prims.list) : FStar_Pprint.document=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 =
          FStarC_List.map (fun d -> FStar_Pprint.op_Hat_Hat h d) ds in
        vconcat uu___3 in
      FStar_Pprint.align uu___2 in
    FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___1 in
  FStar_Pprint.nest (Prims.of_int (2)) uu___
let bulleted (ds : FStar_Pprint.document Prims.list) : FStar_Pprint.document=
  sublist (FStar_Pprint.doc_of_string "- ") ds
let mkmsg (s : Prims.string) : error_message=
  [FStar_Pprint.arbitrary_string s]
let renderdoc (d : FStar_Pprint.document) : Prims.string=
  let one = FStarC_Util.float_of_string "1.0" in
  FStarC_Pprint.pretty_string one (Prims.of_int (80)) d
let backtrace_doc (uu___ : unit) : FStar_Pprint.document=
  let s = FStarC_Util.stack_dump () in
  let uu___1 = text "Stack trace:" in
  FStar_Pprint.op_Hat_Slash_Hat uu___1
    (FStar_Pprint.arbitrary_string (FStarC_Util.trim_string s))
let subdoc' (indent : Prims.bool) (d : FStar_Pprint.document) :
  FStar_Pprint.document=
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
let subdoc (d : FStar_Pprint.document) : FStar_Pprint.document=
  subdoc' true d
let render_as_doc (ds : FStar_Pprint.document Prims.list) :
  FStar_Pprint.document=
  let uu___ = FStarC_List.map (fun d -> subdoc (FStar_Pprint.group d)) ds in
  FStar_Pprint.concat uu___
let rendermsg (ds : FStar_Pprint.document Prims.list) : Prims.string=
  let uu___ = render_as_doc ds in renderdoc uu___
let json_of_error_message (err_msg : FStar_Pprint.document Prims.list) :
  FStarC_Json.json=
  let uu___ =
    FStarC_List.map
      (fun doc -> let uu___1 = renderdoc doc in FStarC_Json.JsonStr uu___1)
      err_msg in
  FStarC_Json.JsonList uu___
