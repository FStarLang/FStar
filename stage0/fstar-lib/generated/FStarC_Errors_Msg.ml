open Prims
type error_message = FStarC_Pprint.document Prims.list
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
      (fun s -> let uu___ = FStarC_Pprint.arbitrary_string s in [uu___])
  }
let (is_error_message_list_doc :
  FStarC_Pprint.document Prims.list is_error_message) =
  { to_doc_list = (fun x -> x) }
let (vconcat : FStarC_Pprint.document Prims.list -> FStarC_Pprint.document) =
  fun ds ->
    match ds with
    | h::t ->
        FStarC_Compiler_List.fold_left
          (fun l ->
             fun r ->
               let uu___ = FStarC_Pprint.op_Hat_Hat FStarC_Pprint.hardline r in
               FStarC_Pprint.op_Hat_Hat l uu___) h t
    | [] -> FStarC_Pprint.empty
let (text : Prims.string -> FStarC_Pprint.document) =
  fun s ->
    let uu___ = FStarC_Pprint.break_ Prims.int_one in
    let uu___1 = FStarC_Pprint.words s in FStarC_Pprint.flow uu___ uu___1
let (sublist :
  FStarC_Pprint.document ->
    FStarC_Pprint.document Prims.list -> FStarC_Pprint.document)
  =
  fun h ->
    fun ds ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              FStarC_Compiler_List.map
                (fun d -> FStarC_Pprint.op_Hat_Hat h d) ds in
            vconcat uu___3 in
          FStarC_Pprint.align uu___2 in
        FStarC_Pprint.op_Hat_Hat FStarC_Pprint.hardline uu___1 in
      FStarC_Pprint.nest (Prims.of_int (2)) uu___
let (bulleted : FStarC_Pprint.document Prims.list -> FStarC_Pprint.document)
  =
  fun ds -> let uu___ = FStarC_Pprint.doc_of_string "- " in sublist uu___ ds
let (mkmsg : Prims.string -> error_message) =
  fun s -> let uu___ = FStarC_Pprint.arbitrary_string s in [uu___]
let (renderdoc : FStarC_Pprint.document -> Prims.string) =
  fun d ->
    let one = FStarC_Compiler_Util.float_of_string "1.0" in
    FStarC_Pprint.pretty_string one (Prims.of_int (80)) d
let (backtrace_doc : unit -> FStarC_Pprint.document) =
  fun uu___ ->
    let s = FStarC_Compiler_Util.stack_dump () in
    let uu___1 = text "Stack trace:" in
    let uu___2 =
      FStarC_Pprint.arbitrary_string (FStarC_Compiler_Util.trim_string s) in
    FStarC_Pprint.op_Hat_Slash_Hat uu___1 uu___2
let (subdoc' :
  Prims.bool -> FStarC_Pprint.document -> FStarC_Pprint.document) =
  fun indent ->
    fun d ->
      if d = FStarC_Pprint.empty
      then FStarC_Pprint.empty
      else
        (let uu___1 =
           if indent
           then FStarC_Pprint.blank (Prims.of_int (2))
           else FStarC_Pprint.empty in
         let uu___2 =
           let uu___3 = FStarC_Pprint.doc_of_string "-" in
           let uu___4 =
             let uu___5 = FStarC_Pprint.blank Prims.int_one in
             let uu___6 =
               let uu___7 = FStarC_Pprint.align d in
               FStarC_Pprint.op_Hat_Hat uu___7 FStarC_Pprint.hardline in
             FStarC_Pprint.op_Hat_Hat uu___5 uu___6 in
           FStarC_Pprint.op_Hat_Hat uu___3 uu___4 in
         FStarC_Pprint.op_Hat_Hat uu___1 uu___2)
let (subdoc : FStarC_Pprint.document -> FStarC_Pprint.document) =
  fun d -> subdoc' true d
let (rendermsg : error_message -> Prims.string) =
  fun ds ->
    let uu___ =
      let uu___1 =
        FStarC_Compiler_List.map
          (fun d -> let uu___2 = FStarC_Pprint.group d in subdoc uu___2) ds in
      FStarC_Pprint.concat uu___1 in
    renderdoc uu___
let (json_of_error_message :
  FStarC_Pprint.document Prims.list -> FStarC_Json.json) =
  fun err_msg ->
    let uu___ =
      FStarC_Compiler_List.map
        (fun doc -> let uu___1 = renderdoc doc in FStarC_Json.JsonStr uu___1)
        err_msg in
    FStarC_Json.JsonList uu___