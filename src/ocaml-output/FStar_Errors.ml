open Prims
exception Err of Prims.string
let uu___is_Err: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Err uu____8 -> true | uu____9 -> false
let __proj__Err__item__uu___: Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | Err uu____17 -> uu____17
exception Error of (Prims.string* FStar_Range.range)
let uu___is_Error: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Error uu____27 -> true | uu____30 -> false
let __proj__Error__item__uu___:
  Prims.exn -> (Prims.string* FStar_Range.range) =
  fun projectee  -> match projectee with | Error uu____42 -> uu____42
exception Warning of (Prims.string* FStar_Range.range)
let uu___is_Warning: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Warning uu____54 -> true | uu____57 -> false
let __proj__Warning__item__uu___:
  Prims.exn -> (Prims.string* FStar_Range.range) =
  fun projectee  -> match projectee with | Warning uu____69 -> uu____69
exception Empty_frag
let uu___is_Empty_frag: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Empty_frag  -> true | uu____76 -> false
type issue_level =
  | ENotImplemented
  | EInfo
  | EWarning
  | EError
let uu___is_ENotImplemented: issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | ENotImplemented  -> true | uu____81 -> false
let uu___is_EInfo: issue_level -> Prims.bool =
  fun projectee  -> match projectee with | EInfo  -> true | uu____86 -> false
let uu___is_EWarning: issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | EWarning  -> true | uu____91 -> false
let uu___is_EError: issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | EError  -> true | uu____96 -> false
type issue =
  {
  issue_message: Prims.string;
  issue_level: issue_level;
  issue_range: FStar_Range.range option;}
type error_handler =
  {
  eh_add_one: issue -> Prims.unit;
  eh_count_errors: Prims.unit -> Prims.int;
  eh_report: Prims.unit -> issue Prims.list;
  eh_clear: Prims.unit -> Prims.unit;}
let format_issue: issue -> Prims.string =
  fun issue  ->
    let level_header =
      match issue.issue_level with
      | EInfo  -> "(Info) "
      | EWarning  -> "(Warning) "
      | EError  -> "(Error) "
      | ENotImplemented  -> "Feature not yet implemented: " in
    let uu____207 =
      match issue.issue_range with
      | None  -> ("", "")
      | Some r ->
          let uu____213 =
            let uu____214 = FStar_Range.string_of_use_range r in
            FStar_Util.format1 "%s: " uu____214 in
          let uu____215 =
            if r.FStar_Range.use_range = r.FStar_Range.def_range
            then ""
            else
              (let uu____217 = FStar_Range.string_of_range r in
               FStar_Util.format1 " (see also %s)" uu____217) in
          (uu____213, uu____215) in
    match uu____207 with
    | (range_str,see_also_str) ->
        FStar_Util.format4 "%s%s%s%s\n" range_str level_header
          issue.issue_message see_also_str
let print_issue: issue -> Prims.unit =
  fun issue  ->
    let uu____224 = format_issue issue in FStar_Util.print_error uu____224
let compare_issues: issue -> issue -> Prims.int =
  fun i1  ->
    fun i2  ->
      match ((i1.issue_range), (i2.issue_range)) with
      | (None ,None ) -> Prims.parse_int "0"
      | (None ,Some uu____237) -> - (Prims.parse_int "1")
      | (Some uu____240,None ) -> Prims.parse_int "1"
      | (Some r1,Some r2) -> FStar_Range.compare_use_range r1 r2
let default_handler: error_handler =
  let errs = FStar_Util.mk_ref [] in
  let add_one e =
    match e.issue_level with
    | EError  ->
        let uu____256 = let uu____258 = FStar_ST.read errs in e :: uu____258 in
        FStar_ST.write errs uu____256
    | uu____266 -> print_issue e in
  let count_errors uu____270 =
    let uu____271 = FStar_ST.read errs in FStar_List.length uu____271 in
  let report uu____282 =
    let sorted1 =
      let uu____285 = FStar_ST.read errs in
      FStar_List.sortWith compare_issues uu____285 in
    FStar_List.iter print_issue sorted1; sorted1 in
  let clear1 uu____294 = FStar_ST.write errs [] in
  {
    eh_add_one = add_one;
    eh_count_errors = count_errors;
    eh_report = report;
    eh_clear = clear1
  }
let current_handler: error_handler FStar_ST.ref =
  FStar_Util.mk_ref default_handler
let mk_issue:
  issue_level -> FStar_Range.range option -> Prims.string -> issue =
  fun level  ->
    fun range  ->
      fun msg  ->
        { issue_message = msg; issue_level = level; issue_range = range }
let get_err_count: Prims.unit -> Prims.int =
  fun uu____322  ->
    let uu____323 =
      let uu____326 = FStar_ST.read current_handler in
      uu____326.eh_count_errors in
    uu____323 ()
let add_one: issue -> Prims.unit =
  fun issue  ->
    FStar_Util.atomically
      (fun uu____333  ->
         let uu____334 =
           let uu____337 = FStar_ST.read current_handler in
           uu____337.eh_add_one in
         uu____334 issue)
let add_many: issue Prims.list -> Prims.unit =
  fun issues  ->
    FStar_Util.atomically
      (fun uu____346  ->
         let uu____347 =
           let uu____350 = FStar_ST.read current_handler in
           uu____350.eh_add_one in
         FStar_List.iter uu____347 issues)
let report_all: Prims.unit -> issue Prims.list =
  fun uu____357  ->
    let uu____358 =
      let uu____362 = FStar_ST.read current_handler in uu____362.eh_report in
    uu____358 ()
let clear: Prims.unit -> Prims.unit =
  fun uu____368  ->
    let uu____369 =
      let uu____372 = FStar_ST.read current_handler in uu____372.eh_clear in
    uu____369 ()
let set_handler: error_handler -> Prims.unit =
  fun handler  ->
    let issues = report_all () in
    clear (); FStar_ST.write current_handler handler; add_many issues
let diag: FStar_Range.range -> Prims.string -> Prims.unit =
  fun r  ->
    fun msg  ->
      let uu____393 = FStar_Options.debug_any () in
      if uu____393 then add_one (mk_issue EInfo (Some r) msg) else ()
let warn: FStar_Range.range -> Prims.string -> Prims.unit =
  fun r  -> fun msg  -> add_one (mk_issue EWarning (Some r) msg)
let err: FStar_Range.range -> Prims.string -> Prims.unit =
  fun r  -> fun msg  -> add_one (mk_issue EError (Some r) msg)
type error_message_prefix =
  {
  set_prefix: Prims.string -> Prims.unit;
  append_prefix: Prims.string -> Prims.string;
  clear_prefix: Prims.unit -> Prims.unit;}
let message_prefix: error_message_prefix =
  let pfx = FStar_Util.mk_ref None in
  let set_prefix s = FStar_ST.write pfx (Some s) in
  let clear_prefix uu____480 = FStar_ST.write pfx None in
  let append_prefix s =
    let uu____488 = FStar_ST.read pfx in
    match uu____488 with
    | None  -> s
    | Some p -> Prims.strcat p (Prims.strcat ": " s) in
  { set_prefix; append_prefix; clear_prefix }
let add_errors: (Prims.string* FStar_Range.range) Prims.list -> Prims.unit =
  fun errs  ->
    FStar_Util.atomically
      (fun uu____504  ->
         FStar_List.iter
           (fun uu____507  ->
              match uu____507 with
              | (msg,r) ->
                  let uu____512 = message_prefix.append_prefix msg in
                  err r uu____512) errs)
let issue_of_exn: Prims.exn -> issue option =
  fun uu___59_517  ->
    match uu___59_517 with
    | Error (msg,r) ->
        let uu____521 =
          let uu____522 = message_prefix.append_prefix msg in
          mk_issue EError (Some r) uu____522 in
        Some uu____521
    | FStar_Util.NYI msg ->
        let uu____524 =
          let uu____525 = message_prefix.append_prefix msg in
          mk_issue ENotImplemented None uu____525 in
        Some uu____524
    | Err msg ->
        let uu____527 =
          let uu____528 = message_prefix.append_prefix msg in
          mk_issue EError None uu____528 in
        Some uu____527
    | uu____529 -> None
let err_exn: Prims.exn -> Prims.unit =
  fun exn  ->
    let uu____534 = issue_of_exn exn in
    match uu____534 with | Some issue -> add_one issue | None  -> raise exn
let handleable: Prims.exn -> Prims.bool =
  fun uu___60_540  ->
    match uu___60_540 with
    | Error uu____541 -> true
    | FStar_Util.NYI uu____544 -> true
    | Err uu____545 -> true
    | uu____546 -> false