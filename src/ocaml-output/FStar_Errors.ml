open Prims
exception Err of Prims.string
let uu___is_Err: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Err uu____6 -> true | uu____7 -> false
let __proj__Err__item__uu___: Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | Err uu____14 -> uu____14
exception Error of (Prims.string* FStar_Range.range)
let uu___is_Error: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Error uu____22 -> true | uu____25 -> false
let __proj__Error__item__uu___:
  Prims.exn -> (Prims.string* FStar_Range.range) =
  fun projectee  -> match projectee with | Error uu____36 -> uu____36
exception Warning of (Prims.string* FStar_Range.range)
let uu___is_Warning: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Warning uu____46 -> true | uu____49 -> false
let __proj__Warning__item__uu___:
  Prims.exn -> (Prims.string* FStar_Range.range) =
  fun projectee  -> match projectee with | Warning uu____60 -> uu____60
exception Empty_frag
let uu___is_Empty_frag: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Empty_frag  -> true | uu____66 -> false
type issue_level =
  | ENotImplemented
  | EInfo
  | EWarning
  | EError
let uu___is_ENotImplemented: issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | ENotImplemented  -> true | uu____70 -> false
let uu___is_EInfo: issue_level -> Prims.bool =
  fun projectee  -> match projectee with | EInfo  -> true | uu____74 -> false
let uu___is_EWarning: issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | EWarning  -> true | uu____78 -> false
let uu___is_EError: issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | EError  -> true | uu____82 -> false
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
    let uu____170 =
      match issue.issue_range with
      | None  -> ("", "")
      | Some r ->
          let uu____176 =
            let uu____177 = FStar_Range.string_of_use_range r in
            FStar_Util.format1 "%s: " uu____177 in
          let uu____178 =
            if r.FStar_Range.use_range = r.FStar_Range.def_range
            then ""
            else
              (let uu____180 = FStar_Range.string_of_range r in
               FStar_Util.format1 " (see also %s)" uu____180) in
          (uu____176, uu____178) in
    match uu____170 with
    | (range_str,see_also_str) ->
        FStar_Util.format4 "%s%s%s%s\n" range_str level_header
          issue.issue_message see_also_str
let print_issue: issue -> Prims.unit =
  fun issue  ->
    let uu____186 = format_issue issue in FStar_Util.print_error uu____186
let compare_issues: issue -> issue -> Prims.int =
  fun i1  ->
    fun i2  ->
      match ((i1.issue_range), (i2.issue_range)) with
      | (None ,None ) -> Prims.parse_int "0"
      | (None ,Some uu____197) -> - (Prims.parse_int "1")
      | (Some uu____200,None ) -> Prims.parse_int "1"
      | (Some r1,Some r2) -> FStar_Range.compare_use_range r1 r2
let default_handler: error_handler =
  let errs = FStar_Util.mk_ref [] in
  let add_one e =
    match e.issue_level with
    | EError  ->
        let uu____216 = let uu____218 = FStar_ST.read errs in e :: uu____218 in
        FStar_ST.write errs uu____216
    | uu____226 -> print_issue e in
  let count_errors uu____230 =
    let uu____231 = FStar_ST.read errs in FStar_List.length uu____231 in
  let report uu____242 =
    let sorted1 =
      let uu____245 = FStar_ST.read errs in
      FStar_List.sortWith compare_issues uu____245 in
    FStar_List.iter print_issue sorted1; sorted1 in
  let clear1 uu____254 = FStar_ST.write errs [] in
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
  fun uu____278  ->
    let uu____279 =
      let uu____282 = FStar_ST.read current_handler in
      uu____282.eh_count_errors in
    uu____279 ()
let add_one: issue -> Prims.unit =
  fun issue  ->
    FStar_Util.atomically
      (fun uu____288  ->
         let uu____289 =
           let uu____292 = FStar_ST.read current_handler in
           uu____292.eh_add_one in
         uu____289 issue)
let add_many: issue Prims.list -> Prims.unit =
  fun issues  ->
    FStar_Util.atomically
      (fun uu____300  ->
         let uu____301 =
           let uu____304 = FStar_ST.read current_handler in
           uu____304.eh_add_one in
         FStar_List.iter uu____301 issues)
let report_all: Prims.unit -> issue Prims.list =
  fun uu____310  ->
    let uu____311 =
      let uu____315 = FStar_ST.read current_handler in uu____315.eh_report in
    uu____311 ()
let clear: Prims.unit -> Prims.unit =
  fun uu____320  ->
    let uu____321 =
      let uu____324 = FStar_ST.read current_handler in uu____324.eh_clear in
    uu____321 ()
let set_handler: error_handler -> Prims.unit =
  fun handler  ->
    let issues = report_all () in
    clear (); FStar_ST.write current_handler handler; add_many issues
let diag: FStar_Range.range -> Prims.string -> Prims.unit =
  fun r  ->
    fun msg  ->
      let uu____342 = FStar_Options.debug_any () in
      if uu____342 then add_one (mk_issue EInfo (Some r) msg) else ()
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
  let clear_prefix uu____413 = FStar_ST.write pfx None in
  let append_prefix s =
    let uu____421 = FStar_ST.read pfx in
    match uu____421 with
    | None  -> s
    | Some p -> Prims.strcat p (Prims.strcat ": " s) in
  { set_prefix; append_prefix; clear_prefix }
let add_errors: (Prims.string* FStar_Range.range) Prims.list -> Prims.unit =
  fun errs  ->
    FStar_Util.atomically
      (fun uu____436  ->
         FStar_List.iter
           (fun uu____439  ->
              match uu____439 with
              | (msg,r) ->
                  let uu____444 = message_prefix.append_prefix msg in
                  err r uu____444) errs)
let issue_of_exn: Prims.exn -> issue option =
  fun uu___59_448  ->
    match uu___59_448 with
    | Error (msg,r) ->
        let uu____452 =
          let uu____453 = message_prefix.append_prefix msg in
          mk_issue EError (Some r) uu____453 in
        Some uu____452
    | FStar_Util.NYI msg ->
        let uu____455 =
          let uu____456 = message_prefix.append_prefix msg in
          mk_issue ENotImplemented None uu____456 in
        Some uu____455
    | Err msg ->
        let uu____458 =
          let uu____459 = message_prefix.append_prefix msg in
          mk_issue EError None uu____459 in
        Some uu____458
    | uu____460 -> None
let err_exn: Prims.exn -> Prims.unit =
  fun exn  ->
    let uu____464 = issue_of_exn exn in
    match uu____464 with | Some issue -> add_one issue | None  -> raise exn
let handleable: Prims.exn -> Prims.bool =
  fun uu___60_469  ->
    match uu___60_469 with
    | Error uu____470 -> true
    | FStar_Util.NYI uu____473 -> true
    | Err uu____474 -> true
    | uu____475 -> false