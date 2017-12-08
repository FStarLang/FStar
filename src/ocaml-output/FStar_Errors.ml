open Prims
exception Err of Prims.string 
let uu___is_Err : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Err uu____7 -> true | uu____8 -> false
  
let __proj__Err__item__uu___ : Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | Err uu____15 -> uu____15 
exception Error of (Prims.string,FStar_Range.range)
  FStar_Pervasives_Native.tuple2 
let uu___is_Error : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Error uu____26 -> true | uu____31 -> false
  
let __proj__Error__item__uu___ :
  Prims.exn ->
    (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Error uu____46 -> uu____46 
exception Warning of (Prims.string,FStar_Range.range)
  FStar_Pervasives_Native.tuple2 
let uu___is_Warning : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Warning uu____61 -> true | uu____66 -> false
  
let __proj__Warning__item__uu___ :
  Prims.exn ->
    (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Warning uu____81 -> uu____81 
exception Stop 
let uu___is_Stop : Prims.exn -> Prims.bool =
  fun projectee  -> match projectee with | Stop  -> true | uu____89 -> false 
exception Empty_frag 
let uu___is_Empty_frag : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Empty_frag  -> true | uu____93 -> false
  
type issue_level =
  | ENotImplemented 
  | EInfo 
  | EWarning 
  | EError [@@deriving show]
let uu___is_ENotImplemented : issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | ENotImplemented  -> true | uu____97 -> false
  
let uu___is_EInfo : issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | EInfo  -> true | uu____101 -> false
  
let uu___is_EWarning : issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | EWarning  -> true | uu____105 -> false
  
let uu___is_EError : issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | EError  -> true | uu____109 -> false
  
type issue =
  {
  issue_message: Prims.string ;
  issue_level: issue_level ;
  issue_range: FStar_Range.range FStar_Pervasives_Native.option }[@@deriving
                                                                   show]
let __proj__Mkissue__item__issue_message : issue -> Prims.string =
  fun projectee  ->
    match projectee with
    | { issue_message = __fname__issue_message;
        issue_level = __fname__issue_level;
        issue_range = __fname__issue_range;_} -> __fname__issue_message
  
let __proj__Mkissue__item__issue_level : issue -> issue_level =
  fun projectee  ->
    match projectee with
    | { issue_message = __fname__issue_message;
        issue_level = __fname__issue_level;
        issue_range = __fname__issue_range;_} -> __fname__issue_level
  
let __proj__Mkissue__item__issue_range :
  issue -> FStar_Range.range FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { issue_message = __fname__issue_message;
        issue_level = __fname__issue_level;
        issue_range = __fname__issue_range;_} -> __fname__issue_range
  
type error_handler =
  {
  eh_add_one: issue -> Prims.unit ;
  eh_count_errors: Prims.unit -> Prims.int ;
  eh_report: Prims.unit -> issue Prims.list ;
  eh_clear: Prims.unit -> Prims.unit }[@@deriving show]
let __proj__Mkerror_handler__item__eh_add_one :
  error_handler -> issue -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { eh_add_one = __fname__eh_add_one;
        eh_count_errors = __fname__eh_count_errors;
        eh_report = __fname__eh_report; eh_clear = __fname__eh_clear;_} ->
        __fname__eh_add_one
  
let __proj__Mkerror_handler__item__eh_count_errors :
  error_handler -> Prims.unit -> Prims.int =
  fun projectee  ->
    match projectee with
    | { eh_add_one = __fname__eh_add_one;
        eh_count_errors = __fname__eh_count_errors;
        eh_report = __fname__eh_report; eh_clear = __fname__eh_clear;_} ->
        __fname__eh_count_errors
  
let __proj__Mkerror_handler__item__eh_report :
  error_handler -> Prims.unit -> issue Prims.list =
  fun projectee  ->
    match projectee with
    | { eh_add_one = __fname__eh_add_one;
        eh_count_errors = __fname__eh_count_errors;
        eh_report = __fname__eh_report; eh_clear = __fname__eh_clear;_} ->
        __fname__eh_report
  
let __proj__Mkerror_handler__item__eh_clear :
  error_handler -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { eh_add_one = __fname__eh_add_one;
        eh_count_errors = __fname__eh_count_errors;
        eh_report = __fname__eh_report; eh_clear = __fname__eh_clear;_} ->
        __fname__eh_clear
  
let format_issue : issue -> Prims.string =
  fun issue  ->
    let level_header =
      match issue.issue_level with
      | EInfo  -> "(Info) "
      | EWarning  -> "(Warning) "
      | EError  -> "(Error) "
      | ENotImplemented  -> "Feature not yet implemented: "  in
    let uu____278 =
      match issue.issue_range with
      | FStar_Pervasives_Native.None  -> ("", "")
      | FStar_Pervasives_Native.Some r ->
          let uu____288 =
            let uu____289 = FStar_Range.string_of_use_range r  in
            FStar_Util.format1 "%s: " uu____289  in
          let uu____290 =
            let uu____291 =
              let uu____292 = FStar_Range.use_range r  in
              let uu____293 = FStar_Range.def_range r  in
              uu____292 = uu____293  in
            if uu____291
            then ""
            else
              (let uu____295 = FStar_Range.string_of_range r  in
               FStar_Util.format1 " (see also %s)" uu____295)
             in
          (uu____288, uu____290)
       in
    match uu____278 with
    | (range_str,see_also_str) ->
        FStar_Util.format4 "%s%s%s%s\n" range_str level_header
          issue.issue_message see_also_str
  
let print_issue : issue -> Prims.unit =
  fun issue  ->
    let uu____301 = format_issue issue  in FStar_Util.print_error uu____301
  
let compare_issues : issue -> issue -> Prims.int =
  fun i1  ->
    fun i2  ->
      match ((i1.issue_range), (i2.issue_range)) with
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
          (Prims.parse_int "0")
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some
         uu____316) -> ~- (Prims.parse_int "1")
      | (FStar_Pervasives_Native.Some uu____321,FStar_Pervasives_Native.None
         ) -> (Prims.parse_int "1")
      | (FStar_Pervasives_Native.Some r1,FStar_Pervasives_Native.Some r2) ->
          FStar_Range.compare_use_range r1 r2
  
let default_handler : error_handler =
  let errs = FStar_Util.mk_ref []  in
  let add_one e =
    match e.issue_level with
    | EError  ->
        let uu____343 =
          let uu____346 = FStar_ST.op_Bang errs  in e :: uu____346  in
        FStar_ST.op_Colon_Equals errs uu____343
    | uu____481 -> print_issue e  in
  let count_errors uu____485 =
    let uu____486 = FStar_ST.op_Bang errs  in FStar_List.length uu____486  in
  let report uu____560 =
    let sorted1 =
      let uu____564 = FStar_ST.op_Bang errs  in
      FStar_List.sortWith compare_issues uu____564  in
    FStar_List.iter print_issue sorted1; sorted1  in
  let clear1 uu____637 = FStar_ST.op_Colon_Equals errs []  in
  {
    eh_add_one = add_one;
    eh_count_errors = count_errors;
    eh_report = report;
    eh_clear = clear1
  } 
let current_handler : error_handler FStar_ST.ref =
  FStar_Util.mk_ref default_handler 
let mk_issue :
  issue_level ->
    FStar_Range.range FStar_Pervasives_Native.option -> Prims.string -> issue
  =
  fun level  ->
    fun range  ->
      fun msg  ->
        { issue_message = msg; issue_level = level; issue_range = range }
  
let get_err_count : Prims.unit -> Prims.int =
  fun uu____732  ->
    let uu____733 =
      let uu____736 = FStar_ST.op_Bang current_handler  in
      uu____736.eh_count_errors  in
    uu____733 ()
  
let add_one : issue -> Prims.unit =
  fun issue  ->
    FStar_Util.atomically
      (fun uu____790  ->
         let uu____791 =
           let uu____794 = FStar_ST.op_Bang current_handler  in
           uu____794.eh_add_one  in
         uu____791 issue)
  
let add_many : issue Prims.list -> Prims.unit =
  fun issues  ->
    FStar_Util.atomically
      (fun uu____852  ->
         let uu____853 =
           let uu____856 = FStar_ST.op_Bang current_handler  in
           uu____856.eh_add_one  in
         FStar_List.iter uu____853 issues)
  
let report_all : Prims.unit -> issue Prims.list =
  fun uu____909  ->
    let uu____910 =
      let uu____915 = FStar_ST.op_Bang current_handler  in
      uu____915.eh_report  in
    uu____910 ()
  
let clear : Prims.unit -> Prims.unit =
  fun uu____966  ->
    let uu____967 =
      let uu____970 = FStar_ST.op_Bang current_handler  in uu____970.eh_clear
       in
    uu____967 ()
  
let set_handler : error_handler -> Prims.unit =
  fun handler  ->
    let issues = report_all ()  in
    clear ();
    FStar_ST.op_Colon_Equals current_handler handler;
    add_many issues
  
let diag : FStar_Range.range -> Prims.string -> Prims.unit =
  fun r  ->
    fun msg  ->
      let uu____1081 = FStar_Options.debug_any ()  in
      if uu____1081
      then add_one (mk_issue EInfo (FStar_Pervasives_Native.Some r) msg)
      else ()
  
let warn : FStar_Range.range -> Prims.string -> Prims.unit =
  fun r  ->
    fun msg  ->
      add_one (mk_issue EWarning (FStar_Pervasives_Native.Some r) msg)
  
let err : FStar_Range.range -> Prims.string -> Prims.unit =
  fun r  ->
    fun msg  ->
      add_one (mk_issue EError (FStar_Pervasives_Native.Some r) msg)
  
type error_message_prefix =
  {
  set_prefix: Prims.string -> Prims.unit ;
  append_prefix: Prims.string -> Prims.string ;
  clear_prefix: Prims.unit -> Prims.unit }[@@deriving show]
let __proj__Mkerror_message_prefix__item__set_prefix :
  error_message_prefix -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { set_prefix = __fname__set_prefix;
        append_prefix = __fname__append_prefix;
        clear_prefix = __fname__clear_prefix;_} -> __fname__set_prefix
  
let __proj__Mkerror_message_prefix__item__append_prefix :
  error_message_prefix -> Prims.string -> Prims.string =
  fun projectee  ->
    match projectee with
    | { set_prefix = __fname__set_prefix;
        append_prefix = __fname__append_prefix;
        clear_prefix = __fname__clear_prefix;_} -> __fname__append_prefix
  
let __proj__Mkerror_message_prefix__item__clear_prefix :
  error_message_prefix -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { set_prefix = __fname__set_prefix;
        append_prefix = __fname__append_prefix;
        clear_prefix = __fname__clear_prefix;_} -> __fname__clear_prefix
  
let message_prefix : error_message_prefix =
  let pfx = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  let set_prefix s =
    FStar_ST.op_Colon_Equals pfx (FStar_Pervasives_Native.Some s)  in
  let clear_prefix uu____1247 =
    FStar_ST.op_Colon_Equals pfx FStar_Pervasives_Native.None  in
  let append_prefix s =
    let uu____1318 = FStar_ST.op_Bang pfx  in
    match uu____1318 with
    | FStar_Pervasives_Native.None  -> s
    | FStar_Pervasives_Native.Some p -> Prims.strcat p (Prims.strcat ": " s)
     in
  { set_prefix; append_prefix; clear_prefix } 
let add_errors :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> Prims.unit
  =
  fun errs  ->
    FStar_Util.atomically
      (fun uu____1404  ->
         FStar_List.iter
           (fun uu____1413  ->
              match uu____1413 with
              | (msg,r) ->
                  let uu____1420 = message_prefix.append_prefix msg  in
                  err r uu____1420) errs)
  
let issue_of_exn : Prims.exn -> issue FStar_Pervasives_Native.option =
  fun uu___37_1425  ->
    match uu___37_1425 with
    | Error (msg,r) ->
        let uu____1430 =
          let uu____1431 = message_prefix.append_prefix msg  in
          mk_issue EError (FStar_Pervasives_Native.Some r) uu____1431  in
        FStar_Pervasives_Native.Some uu____1430
    | FStar_Util.NYI msg ->
        let uu____1433 =
          let uu____1434 = message_prefix.append_prefix msg  in
          mk_issue ENotImplemented FStar_Pervasives_Native.None uu____1434
           in
        FStar_Pervasives_Native.Some uu____1433
    | Err msg ->
        let uu____1436 =
          let uu____1437 = message_prefix.append_prefix msg  in
          mk_issue EError FStar_Pervasives_Native.None uu____1437  in
        FStar_Pervasives_Native.Some uu____1436
    | uu____1438 -> FStar_Pervasives_Native.None
  
let err_exn : Prims.exn -> Prims.unit =
  fun exn  ->
    if exn = Stop
    then ()
    else
      (let uu____1443 = issue_of_exn exn  in
       match uu____1443 with
       | FStar_Pervasives_Native.Some issue -> add_one issue
       | FStar_Pervasives_Native.None  -> FStar_Exn.raise exn)
  
let handleable : Prims.exn -> Prims.bool =
  fun uu___38_1449  ->
    match uu___38_1449 with
    | Error uu____1450 -> true
    | FStar_Util.NYI uu____1455 -> true
    | Stop  -> true
    | Err uu____1456 -> true
    | uu____1457 -> false
  
let stop_if_err : Prims.unit -> Prims.unit =
  fun uu____1460  ->
    let uu____1461 =
      let uu____1462 = get_err_count ()  in
      uu____1462 > (Prims.parse_int "0")  in
    if uu____1461 then FStar_Exn.raise Stop else ()
  