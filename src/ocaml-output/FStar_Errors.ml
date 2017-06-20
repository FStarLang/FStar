open Prims
exception Err of Prims.string 
let uu___is_Err : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Err uu____8 -> true | uu____9 -> false
  
let __proj__Err__item__uu___ : Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | Err uu____17 -> uu____17 
exception Error of (Prims.string * FStar_Range.range) 
let uu___is_Error : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Error uu____27 -> true | uu____30 -> false
  
let __proj__Error__item__uu___ :
  Prims.exn -> (Prims.string * FStar_Range.range) =
  fun projectee  -> match projectee with | Error uu____42 -> uu____42 
exception Warning of (Prims.string * FStar_Range.range) 
let uu___is_Warning : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Warning uu____54 -> true | uu____57 -> false
  
let __proj__Warning__item__uu___ :
  Prims.exn -> (Prims.string * FStar_Range.range) =
  fun projectee  -> match projectee with | Warning uu____69 -> uu____69 
exception Empty_frag 
let uu___is_Empty_frag : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Empty_frag  -> true | uu____76 -> false
  
type issue_level =
  | ENotImplemented 
  | EInfo 
  | EWarning 
  | EError 
let uu___is_ENotImplemented : issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | ENotImplemented  -> true | uu____81 -> false
  
let uu___is_EInfo : issue_level -> Prims.bool =
  fun projectee  -> match projectee with | EInfo  -> true | uu____86 -> false 
let uu___is_EWarning : issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | EWarning  -> true | uu____91 -> false
  
let uu___is_EError : issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | EError  -> true | uu____96 -> false
  
type issue =
  {
  issue_message: Prims.string ;
  issue_level: issue_level ;
  issue_range: FStar_Range.range option }
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
  
let __proj__Mkissue__item__issue_range : issue -> FStar_Range.range option =
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
  eh_clear: Prims.unit -> Prims.unit }
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
    let uu____264 =
      match issue.issue_range with
      | None  -> ("", "")
      | Some r ->
          let uu____270 =
            let uu____271 = FStar_Range.string_of_use_range r  in
            FStar_Util.format1 "%s: " uu____271  in
          let uu____272 =
            if r.FStar_Range.use_range = r.FStar_Range.def_range
            then ""
            else
              (let uu____274 = FStar_Range.string_of_range r  in
               FStar_Util.format1 " (see also %s)" uu____274)
             in
          (uu____270, uu____272)
       in
    match uu____264 with
    | (range_str,see_also_str) ->
        FStar_Util.format4 "%s%s%s%s\n" range_str level_header
          issue.issue_message see_also_str
  
let print_issue : issue -> Prims.unit =
  fun issue  ->
    let uu____281 = format_issue issue  in FStar_Util.print_error uu____281
  
let compare_issues : issue -> issue -> Prims.int =
  fun i1  ->
    fun i2  ->
      match ((i1.issue_range), (i2.issue_range)) with
      | (None ,None ) -> (Prims.parse_int "0")
      | (None ,Some uu____294) -> ~- (Prims.parse_int "1")
      | (Some uu____297,None ) -> (Prims.parse_int "1")
      | (Some r1,Some r2) -> FStar_Range.compare_use_range r1 r2
  
let default_handler : error_handler =
  let errs = FStar_Util.mk_ref []  in
  let add_one e =
    match e.issue_level with
    | EError  ->
        let uu____313 = let uu____315 = FStar_ST.read errs  in e :: uu____315
           in
        FStar_ST.write errs uu____313
    | uu____323 -> print_issue e  in
  let count_errors uu____327 =
    let uu____328 = FStar_ST.read errs  in FStar_List.length uu____328  in
  let report uu____339 =
    let sorted1 =
      let uu____342 = FStar_ST.read errs  in
      FStar_List.sortWith compare_issues uu____342  in
    FStar_List.iter print_issue sorted1; sorted1  in
  let clear1 uu____351 = FStar_ST.write errs []  in
  {
    eh_add_one = add_one;
    eh_count_errors = count_errors;
    eh_report = report;
    eh_clear = clear1
  } 
let current_handler : error_handler FStar_ST.ref =
  FStar_Util.mk_ref default_handler 
let mk_issue :
  issue_level -> FStar_Range.range option -> Prims.string -> issue =
  fun level  ->
    fun range  ->
      fun msg  ->
        { issue_message = msg; issue_level = level; issue_range = range }
  
let get_err_count : Prims.unit -> Prims.int =
  fun uu____379  ->
    let uu____380 =
      let uu____383 = FStar_ST.read current_handler  in
      uu____383.eh_count_errors  in
    uu____380 ()
  
let add_one : issue -> Prims.unit =
  fun issue  ->
    FStar_Util.atomically
      (fun uu____390  ->
         let uu____391 =
           let uu____394 = FStar_ST.read current_handler  in
           uu____394.eh_add_one  in
         uu____391 issue)
  
let add_many : issue Prims.list -> Prims.unit =
  fun issues  ->
    FStar_Util.atomically
      (fun uu____403  ->
         let uu____404 =
           let uu____407 = FStar_ST.read current_handler  in
           uu____407.eh_add_one  in
         FStar_List.iter uu____404 issues)
  
let report_all : Prims.unit -> issue Prims.list =
  fun uu____414  ->
    let uu____415 =
      let uu____419 = FStar_ST.read current_handler  in uu____419.eh_report
       in
    uu____415 ()
  
let clear : Prims.unit -> Prims.unit =
  fun uu____425  ->
    let uu____426 =
      let uu____429 = FStar_ST.read current_handler  in uu____429.eh_clear
       in
    uu____426 ()
  
let set_handler : error_handler -> Prims.unit =
  fun handler  ->
    let issues = report_all ()  in
    clear (); FStar_ST.write current_handler handler; add_many issues
  
let diag : FStar_Range.range -> Prims.string -> Prims.unit =
  fun r  ->
    fun msg  ->
      let uu____450 = FStar_Options.debug_any ()  in
      if uu____450 then add_one (mk_issue EInfo (Some r) msg) else ()
  
let warn : FStar_Range.range -> Prims.string -> Prims.unit =
  fun r  -> fun msg  -> add_one (mk_issue EWarning (Some r) msg) 
let err : FStar_Range.range -> Prims.string -> Prims.unit =
  fun r  -> fun msg  -> add_one (mk_issue EError (Some r) msg) 
type error_message_prefix =
  {
  set_prefix: Prims.string -> Prims.unit ;
  append_prefix: Prims.string -> Prims.string ;
  clear_prefix: Prims.unit -> Prims.unit }
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
  let pfx = FStar_Util.mk_ref None  in
  let set_prefix s = FStar_ST.write pfx (Some s)  in
  let clear_prefix uu____561 = FStar_ST.write pfx None  in
  let append_prefix s =
    let uu____569 = FStar_ST.read pfx  in
    match uu____569 with
    | None  -> s
    | Some p -> Prims.strcat p (Prims.strcat ": " s)  in
  { set_prefix; append_prefix; clear_prefix } 
let add_errors : (Prims.string * FStar_Range.range) Prims.list -> Prims.unit
  =
  fun errs  ->
    FStar_Util.atomically
      (fun uu____585  ->
         FStar_List.iter
           (fun uu____588  ->
              match uu____588 with
              | (msg,r) ->
                  let uu____593 = message_prefix.append_prefix msg  in
                  err r uu____593) errs)
  
let issue_of_exn : Prims.exn -> issue option =
  fun uu___59_598  ->
    match uu___59_598 with
    | Error (msg,r) ->
        let uu____602 =
          let uu____603 = message_prefix.append_prefix msg  in
          mk_issue EError (Some r) uu____603  in
        Some uu____602
    | FStar_Util.NYI msg ->
        let uu____605 =
          let uu____606 = message_prefix.append_prefix msg  in
          mk_issue ENotImplemented None uu____606  in
        Some uu____605
    | Err msg ->
        let uu____608 =
          let uu____609 = message_prefix.append_prefix msg  in
          mk_issue EError None uu____609  in
        Some uu____608
    | uu____610 -> None
  
let err_exn : Prims.exn -> Prims.unit =
  fun exn  ->
    let uu____615 = issue_of_exn exn  in
    match uu____615 with | Some issue -> add_one issue | None  -> raise exn
  
let handleable : Prims.exn -> Prims.bool =
  fun uu___60_621  ->
    match uu___60_621 with
    | Error uu____622 -> true
    | FStar_Util.NYI uu____625 -> true
    | Err uu____626 -> true
    | uu____627 -> false
  