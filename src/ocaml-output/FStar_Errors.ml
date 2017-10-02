open Prims
exception Err of Prims.string
let uu___is_Err: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Err uu____8 -> true | uu____9 -> false
let __proj__Err__item__uu___: Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | Err uu____17 -> uu____17
exception Error of (Prims.string,FStar_Range.range)
  FStar_Pervasives_Native.tuple2
let uu___is_Error: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Error uu____29 -> true | uu____34 -> false
let __proj__Error__item__uu___:
  Prims.exn ->
    (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Error uu____50 -> uu____50
exception Warning of (Prims.string,FStar_Range.range)
  FStar_Pervasives_Native.tuple2
let uu___is_Warning: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Warning uu____66 -> true | uu____71 -> false
let __proj__Warning__item__uu___:
  Prims.exn ->
    (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Warning uu____87 -> uu____87
exception Empty_frag
let uu___is_Empty_frag: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Empty_frag  -> true | uu____96 -> false
type issue_level =
  | ENotImplemented
  | EInfo
  | EWarning
  | EError[@@deriving show]
let uu___is_ENotImplemented: issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | ENotImplemented  -> true | uu____101 -> false
let uu___is_EInfo: issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | EInfo  -> true | uu____106 -> false
let uu___is_EWarning: issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | EWarning  -> true | uu____111 -> false
let uu___is_EError: issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | EError  -> true | uu____116 -> false
type issue =
  {
  issue_message: Prims.string;
  issue_level: issue_level;
  issue_range: FStar_Range.range FStar_Pervasives_Native.option;}[@@deriving
                                                                   show]
let __proj__Mkissue__item__issue_message: issue -> Prims.string =
  fun projectee  ->
    match projectee with
    | { issue_message = __fname__issue_message;
        issue_level = __fname__issue_level;
        issue_range = __fname__issue_range;_} -> __fname__issue_message
let __proj__Mkissue__item__issue_level: issue -> issue_level =
  fun projectee  ->
    match projectee with
    | { issue_message = __fname__issue_message;
        issue_level = __fname__issue_level;
        issue_range = __fname__issue_range;_} -> __fname__issue_level
let __proj__Mkissue__item__issue_range:
  issue -> FStar_Range.range FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { issue_message = __fname__issue_message;
        issue_level = __fname__issue_level;
        issue_range = __fname__issue_range;_} -> __fname__issue_range
type error_handler =
  {
  eh_add_one: issue -> Prims.unit;
  eh_count_errors: Prims.unit -> Prims.int;
  eh_report: Prims.unit -> issue Prims.list;
  eh_clear: Prims.unit -> Prims.unit;}[@@deriving show]
let __proj__Mkerror_handler__item__eh_add_one:
  error_handler -> issue -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { eh_add_one = __fname__eh_add_one;
        eh_count_errors = __fname__eh_count_errors;
        eh_report = __fname__eh_report; eh_clear = __fname__eh_clear;_} ->
        __fname__eh_add_one
let __proj__Mkerror_handler__item__eh_count_errors:
  error_handler -> Prims.unit -> Prims.int =
  fun projectee  ->
    match projectee with
    | { eh_add_one = __fname__eh_add_one;
        eh_count_errors = __fname__eh_count_errors;
        eh_report = __fname__eh_report; eh_clear = __fname__eh_clear;_} ->
        __fname__eh_count_errors
let __proj__Mkerror_handler__item__eh_report:
  error_handler -> Prims.unit -> issue Prims.list =
  fun projectee  ->
    match projectee with
    | { eh_add_one = __fname__eh_add_one;
        eh_count_errors = __fname__eh_count_errors;
        eh_report = __fname__eh_report; eh_clear = __fname__eh_clear;_} ->
        __fname__eh_report
let __proj__Mkerror_handler__item__eh_clear:
  error_handler -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { eh_add_one = __fname__eh_add_one;
        eh_count_errors = __fname__eh_count_errors;
        eh_report = __fname__eh_report; eh_clear = __fname__eh_clear;_} ->
        __fname__eh_clear
let format_issue: issue -> Prims.string =
  fun issue  ->
    let level_header =
      match issue.issue_level with
      | EInfo  -> "(Info) "
      | EWarning  -> "(Warning) "
      | EError  -> "(Error) "
      | ENotImplemented  -> "Feature not yet implemented: " in
    let uu____297 =
      match issue.issue_range with
      | FStar_Pervasives_Native.None  -> ("", "")
      | FStar_Pervasives_Native.Some r ->
          let uu____307 =
            let uu____308 = FStar_Range.string_of_use_range r in
            FStar_Util.format1 "%s: " uu____308 in
          let uu____309 =
            if r.FStar_Range.use_range = r.FStar_Range.def_range
            then ""
            else
              (let uu____311 = FStar_Range.string_of_range r in
               FStar_Util.format1 " (see also %s)" uu____311) in
          (uu____307, uu____309) in
    match uu____297 with
    | (range_str,see_also_str) ->
        FStar_Util.format4 "%s%s%s%s\n" range_str level_header
          issue.issue_message see_also_str
let print_issue: issue -> Prims.unit =
  fun issue  ->
    let uu____318 = format_issue issue in FStar_Util.print_error uu____318
let compare_issues: issue -> issue -> Prims.int =
  fun i1  ->
    fun i2  ->
      match ((i1.issue_range), (i2.issue_range)) with
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
          Prims.parse_int "0"
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some
         uu____335) -> - (Prims.parse_int "1")
      | (FStar_Pervasives_Native.Some uu____340,FStar_Pervasives_Native.None
         ) -> Prims.parse_int "1"
      | (FStar_Pervasives_Native.Some r1,FStar_Pervasives_Native.Some r2) ->
          FStar_Range.compare_use_range r1 r2
let default_handler: error_handler =
  let errs = FStar_Util.mk_ref [] in
  let add_one e =
    match e.issue_level with
    | EError  ->
        let uu____362 =
          let uu____365 = FStar_ST.op_Bang errs in e :: uu____365 in
        FStar_ST.op_Colon_Equals errs uu____362
    | uu____496 -> print_issue e in
  let count_errors uu____500 =
    let uu____501 = FStar_ST.op_Bang errs in FStar_List.length uu____501 in
  let report uu____573 =
    let sorted1 =
      let uu____577 = FStar_ST.op_Bang errs in
      FStar_List.sortWith compare_issues uu____577 in
    FStar_List.iter print_issue sorted1; sorted1 in
  let clear1 uu____648 = FStar_ST.op_Colon_Equals errs [] in
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
  fun uu____745  ->
    let uu____746 =
      let uu____749 = FStar_ST.op_Bang current_handler in
      uu____749.eh_count_errors in
    uu____746 ()
let add_one: issue -> Prims.unit =
  fun issue  ->
    FStar_Util.atomically
      (fun uu____802  ->
         let uu____803 =
           let uu____806 = FStar_ST.op_Bang current_handler in
           uu____806.eh_add_one in
         uu____803 issue)
let add_many: issue Prims.list -> Prims.unit =
  fun issues  ->
    FStar_Util.atomically
      (fun uu____863  ->
         let uu____864 =
           let uu____867 = FStar_ST.op_Bang current_handler in
           uu____867.eh_add_one in
         FStar_List.iter uu____864 issues)
let report_all: Prims.unit -> issue Prims.list =
  fun uu____919  ->
    let uu____920 =
      let uu____925 = FStar_ST.op_Bang current_handler in uu____925.eh_report in
    uu____920 ()
let clear: Prims.unit -> Prims.unit =
  fun uu____975  ->
    let uu____976 =
      let uu____979 = FStar_ST.op_Bang current_handler in uu____979.eh_clear in
    uu____976 ()
let set_handler: error_handler -> Prims.unit =
  fun handler  ->
    let issues = report_all () in
    clear ();
    FStar_ST.op_Colon_Equals current_handler handler;
    add_many issues
let diag: FStar_Range.range -> Prims.string -> Prims.unit =
  fun r  ->
    fun msg  ->
      let uu____1089 = FStar_Options.debug_any () in
      if uu____1089
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
  clear_prefix: Prims.unit -> Prims.unit;}[@@deriving show]
let __proj__Mkerror_message_prefix__item__set_prefix:
  error_message_prefix -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { set_prefix = __fname__set_prefix;
        append_prefix = __fname__append_prefix;
        clear_prefix = __fname__clear_prefix;_} -> __fname__set_prefix
let __proj__Mkerror_message_prefix__item__append_prefix:
  error_message_prefix -> Prims.string -> Prims.string =
  fun projectee  ->
    match projectee with
    | { set_prefix = __fname__set_prefix;
        append_prefix = __fname__append_prefix;
        clear_prefix = __fname__clear_prefix;_} -> __fname__append_prefix
let __proj__Mkerror_message_prefix__item__clear_prefix:
  error_message_prefix -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { set_prefix = __fname__set_prefix;
        append_prefix = __fname__append_prefix;
        clear_prefix = __fname__clear_prefix;_} -> __fname__clear_prefix
let message_prefix: error_message_prefix =
  let pfx = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let set_prefix s =
    FStar_ST.op_Colon_Equals pfx (FStar_Pervasives_Native.Some s) in
  let clear_prefix uu____1263 =
    FStar_ST.op_Colon_Equals pfx FStar_Pervasives_Native.None in
  let append_prefix s =
    let uu____1332 = FStar_ST.op_Bang pfx in
    match uu____1332 with
    | FStar_Pervasives_Native.None  -> s
    | FStar_Pervasives_Native.Some p -> Prims.strcat p (Prims.strcat ": " s) in
  { set_prefix; append_prefix; clear_prefix }
let add_errors:
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> Prims.unit
  =
  fun errs  ->
    FStar_Util.atomically
      (fun uu____1417  ->
         FStar_List.iter
           (fun uu____1426  ->
              match uu____1426 with
              | (msg,r) ->
                  let uu____1433 = message_prefix.append_prefix msg in
                  err r uu____1433) errs)
let issue_of_exn: Prims.exn -> issue FStar_Pervasives_Native.option =
  fun uu___59_1439  ->
    match uu___59_1439 with
    | Error (msg,r) ->
        let uu____1444 =
          let uu____1445 = message_prefix.append_prefix msg in
          mk_issue EError (FStar_Pervasives_Native.Some r) uu____1445 in
        FStar_Pervasives_Native.Some uu____1444
    | FStar_Util.NYI msg ->
        let uu____1447 =
          let uu____1448 = message_prefix.append_prefix msg in
          mk_issue ENotImplemented FStar_Pervasives_Native.None uu____1448 in
        FStar_Pervasives_Native.Some uu____1447
    | Err msg ->
        let uu____1450 =
          let uu____1451 = message_prefix.append_prefix msg in
          mk_issue EError FStar_Pervasives_Native.None uu____1451 in
        FStar_Pervasives_Native.Some uu____1450
    | uu____1452 -> FStar_Pervasives_Native.None
let err_exn: Prims.exn -> Prims.unit =
  fun exn  ->
    let uu____1457 = issue_of_exn exn in
    match uu____1457 with
    | FStar_Pervasives_Native.Some issue -> add_one issue
    | FStar_Pervasives_Native.None  -> FStar_Exn.raise exn
let handleable: Prims.exn -> Prims.bool =
  fun uu___60_1464  ->
    match uu___60_1464 with
    | Error uu____1465 -> true
    | FStar_Util.NYI uu____1470 -> true
    | Err uu____1471 -> true
    | uu____1472 -> false