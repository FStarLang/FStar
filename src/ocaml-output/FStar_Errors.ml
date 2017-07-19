open Prims
exception Err of Prims.string
let uu___is_Err: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Err uu____7 -> true | uu____8 -> false
let __proj__Err__item__uu___: Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | Err uu____15 -> uu____15
exception Error of (Prims.string,FStar_Range.range)
  FStar_Pervasives_Native.tuple2
let uu___is_Error: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Error uu____26 -> true | uu____31 -> false
let __proj__Error__item__uu___:
  Prims.exn ->
    (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Error uu____46 -> uu____46
exception Warning of (Prims.string,FStar_Range.range)
  FStar_Pervasives_Native.tuple2
let uu___is_Warning: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Warning uu____61 -> true | uu____66 -> false
let __proj__Warning__item__uu___:
  Prims.exn ->
    (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Warning uu____81 -> uu____81
exception Empty_frag
let uu___is_Empty_frag: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Empty_frag  -> true | uu____89 -> false
type issue_level =
  | ENotImplemented
  | EInfo
  | EWarning
  | EError
let uu___is_ENotImplemented: issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | ENotImplemented  -> true | uu____93 -> false
let uu___is_EInfo: issue_level -> Prims.bool =
  fun projectee  -> match projectee with | EInfo  -> true | uu____97 -> false
let uu___is_EWarning: issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | EWarning  -> true | uu____101 -> false
let uu___is_EError: issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | EError  -> true | uu____105 -> false
type issue =
  {
  issue_message: Prims.string;
  issue_level: issue_level;
  issue_range: FStar_Range.range FStar_Pervasives_Native.option;}
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
    let uu____210 =
      match issue.issue_range with
      | FStar_Pervasives_Native.None  -> ("", "")
      | FStar_Pervasives_Native.Some r ->
          let uu____220 =
            let uu____221 = FStar_Range.string_of_use_range r in
            FStar_Util.format1 "%s: " uu____221 in
          let uu____222 =
            if r.FStar_Range.use_range = r.FStar_Range.def_range
            then ""
            else
              (let uu____224 = FStar_Range.string_of_range r in
               FStar_Util.format1 " (see also %s)" uu____224) in
          (uu____220, uu____222) in
    match uu____210 with
    | (range_str,see_also_str) ->
        FStar_Util.format4 "%s%s%s%s\n" range_str level_header
          issue.issue_message see_also_str
let print_issue: issue -> Prims.unit =
  fun issue  ->
    let uu____230 = format_issue issue in FStar_Util.print_error uu____230
let compare_issues: issue -> issue -> Prims.int =
  fun i1  ->
    fun i2  ->
      match ((i1.issue_range), (i2.issue_range)) with
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
          Prims.parse_int "0"
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some
         uu____245) -> - (Prims.parse_int "1")
      | (FStar_Pervasives_Native.Some uu____250,FStar_Pervasives_Native.None
         ) -> Prims.parse_int "1"
      | (FStar_Pervasives_Native.Some r1,FStar_Pervasives_Native.Some r2) ->
          FStar_Range.compare_use_range r1 r2
let default_handler: error_handler =
  let errs = FStar_Util.mk_ref [] in
  let add_one e =
    match e.issue_level with
    | EError  ->
        let uu____272 = let uu____275 = FStar_ST.read errs in e :: uu____275 in
        FStar_ST.write errs uu____272
    | uu____286 -> print_issue e in
  let count_errors uu____290 =
    let uu____291 = FStar_ST.read errs in FStar_List.length uu____291 in
  let report uu____303 =
    let sorted1 =
      let uu____307 = FStar_ST.read errs in
      FStar_List.sortWith compare_issues uu____307 in
    FStar_List.iter print_issue sorted1; sorted1 in
  let clear1 uu____318 = FStar_ST.write errs [] in
  {
    eh_add_one = add_one;
    eh_count_errors = count_errors;
    eh_report = report;
    eh_clear = clear1
  }
let current_handler: error_handler FStar_ST.ref =
  FStar_Util.mk_ref default_handler
let mk_issue:
  issue_level ->
    FStar_Range.range FStar_Pervasives_Native.option -> Prims.string -> issue
  =
  fun level  ->
    fun range  ->
      fun msg  ->
        { issue_message = msg; issue_level = level; issue_range = range }
let get_err_count: Prims.unit -> Prims.int =
  fun uu____343  ->
    let uu____344 =
      let uu____347 = FStar_ST.read current_handler in
      uu____347.eh_count_errors in
    uu____344 ()
let add_one: issue -> Prims.unit =
  fun issue  ->
    FStar_Util.atomically
      (fun uu____351  ->
         let uu____352 =
           let uu____355 = FStar_ST.read current_handler in
           uu____355.eh_add_one in
         uu____352 issue)
let add_many: issue Prims.list -> Prims.unit =
  fun issues  ->
    FStar_Util.atomically
      (fun uu____363  ->
         let uu____364 =
           let uu____367 = FStar_ST.read current_handler in
           uu____367.eh_add_one in
         FStar_List.iter uu____364 issues)
let report_all: Prims.unit -> issue Prims.list =
  fun uu____372  ->
    let uu____373 =
      let uu____378 = FStar_ST.read current_handler in uu____378.eh_report in
    uu____373 ()
let clear: Prims.unit -> Prims.unit =
  fun uu____381  ->
    let uu____382 =
      let uu____385 = FStar_ST.read current_handler in uu____385.eh_clear in
    uu____382 ()
let set_handler: error_handler -> Prims.unit =
  fun handler  ->
    let issues = report_all () in
    clear (); FStar_ST.write current_handler handler; add_many issues
let diag: FStar_Range.range -> Prims.string -> Prims.unit =
  fun r  ->
    fun msg  ->
      let uu____400 = FStar_Options.debug_any () in
      if uu____400
      then add_one (mk_issue EInfo (FStar_Pervasives_Native.Some r) msg)
      else ()
let warn: FStar_Range.range -> Prims.string -> Prims.unit =
  fun r  ->
    fun msg  ->
      add_one (mk_issue EWarning (FStar_Pervasives_Native.Some r) msg)
let err: FStar_Range.range -> Prims.string -> Prims.unit =
  fun r  ->
    fun msg  ->
      add_one (mk_issue EError (FStar_Pervasives_Native.Some r) msg)
type error_message_prefix =
  {
  set_prefix: Prims.string -> Prims.unit;
  append_prefix: Prims.string -> Prims.string;
  clear_prefix: Prims.unit -> Prims.unit;}
let message_prefix: error_message_prefix =
  let pfx = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let set_prefix s = FStar_ST.write pfx (FStar_Pervasives_Native.Some s) in
  let clear_prefix uu____480 =
    FStar_ST.write pfx FStar_Pervasives_Native.None in
  let append_prefix s =
    let uu____489 = FStar_ST.read pfx in
    match uu____489 with
    | FStar_Pervasives_Native.None  -> s
    | FStar_Pervasives_Native.Some p -> Prims.strcat p (Prims.strcat ": " s) in
  { set_prefix; append_prefix; clear_prefix }
let add_errors:
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> Prims.unit
  =
  fun errs  ->
    FStar_Util.atomically
      (fun uu____512  ->
         FStar_List.iter
           (fun uu____517  ->
              match uu____517 with
              | (msg,r) ->
                  let uu____524 = message_prefix.append_prefix msg in
                  err r uu____524) errs)
let issue_of_exn: Prims.exn -> issue FStar_Pervasives_Native.option =
  fun uu___59_529  ->
    match uu___59_529 with
    | Error (msg,r) ->
        let uu____534 =
          let uu____535 = message_prefix.append_prefix msg in
          mk_issue EError (FStar_Pervasives_Native.Some r) uu____535 in
        FStar_Pervasives_Native.Some uu____534
    | FStar_Util.NYI msg ->
        let uu____537 =
          let uu____538 = message_prefix.append_prefix msg in
          mk_issue ENotImplemented FStar_Pervasives_Native.None uu____538 in
        FStar_Pervasives_Native.Some uu____537
    | Err msg ->
        let uu____540 =
          let uu____541 = message_prefix.append_prefix msg in
          mk_issue EError FStar_Pervasives_Native.None uu____541 in
        FStar_Pervasives_Native.Some uu____540
    | uu____542 -> FStar_Pervasives_Native.None
let err_exn: Prims.exn -> Prims.unit =
  fun exn  ->
    let uu____546 = issue_of_exn exn in
    match uu____546 with
    | FStar_Pervasives_Native.Some issue -> add_one issue
    | FStar_Pervasives_Native.None  -> raise exn
let handleable: Prims.exn -> Prims.bool =
  fun uu___60_552  ->
    match uu___60_552 with
    | Error uu____553 -> true
    | FStar_Util.NYI uu____558 -> true
    | Err uu____559 -> true
    | uu____560 -> false