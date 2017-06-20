open Prims
exception Err of Prims.string
let uu___is_Err: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Err uu____7 -> true | uu____8 -> false
let __proj__Err__item__uu___: Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | Err uu____15 -> uu____15
exception Error of (Prims.string* FStar_Range.range)
let uu___is_Error: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Error uu____24 -> true | uu____27 -> false
let __proj__Error__item__uu___:
  Prims.exn -> (Prims.string* FStar_Range.range) =
  fun projectee  -> match projectee with | Error uu____38 -> uu____38
exception Warning of (Prims.string* FStar_Range.range)
let uu___is_Warning: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Warning uu____49 -> true | uu____52 -> false
let __proj__Warning__item__uu___:
  Prims.exn -> (Prims.string* FStar_Range.range) =
  fun projectee  -> match projectee with | Warning uu____63 -> uu____63
exception Empty_frag
let uu___is_Empty_frag: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Empty_frag  -> true | uu____69 -> false
type issue_level =
  | ENotImplemented
  | EInfo
  | EWarning
  | EError
let uu___is_ENotImplemented: issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | ENotImplemented  -> true | uu____73 -> false
let uu___is_EInfo: issue_level -> Prims.bool =
  fun projectee  -> match projectee with | EInfo  -> true | uu____77 -> false
let uu___is_EWarning: issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | EWarning  -> true | uu____81 -> false
let uu___is_EError: issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | EError  -> true | uu____85 -> false
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
    let uu____184 =
      match issue.issue_range with
      | None  -> ("", "")
      | Some r ->
          let uu____190 =
            let uu____191 = FStar_Range.string_of_use_range r in
            FStar_Util.format1 "%s: " uu____191 in
          let uu____192 =
            if r.FStar_Range.use_range = r.FStar_Range.def_range
            then ""
            else
              (let uu____194 = FStar_Range.string_of_range r in
               FStar_Util.format1 " (see also %s)" uu____194) in
          (uu____190, uu____192) in
    match uu____184 with
    | (range_str,see_also_str) ->
        FStar_Util.format4 "%s%s%s%s\n" range_str level_header
          issue.issue_message see_also_str
let print_issue: issue -> Prims.unit =
  fun issue  ->
    let uu____200 = format_issue issue in FStar_Util.print_error uu____200
let compare_issues: issue -> issue -> Prims.int =
  fun i1  ->
    fun i2  ->
      match ((i1.issue_range), (i2.issue_range)) with
      | (None ,None ) -> Prims.parse_int "0"
      | (None ,Some uu____211) -> - (Prims.parse_int "1")
      | (Some uu____214,None ) -> Prims.parse_int "1"
      | (Some r1,Some r2) -> FStar_Range.compare_use_range r1 r2
let default_handler: error_handler =
  let errs = FStar_Util.mk_ref [] in
  let add_one e =
    match e.issue_level with
    | EError  ->
        let uu____230 = let uu____232 = FStar_ST.read errs in e :: uu____232 in
        FStar_ST.write errs uu____230
    | uu____240 -> print_issue e in
  let count_errors uu____244 =
    let uu____245 = FStar_ST.read errs in FStar_List.length uu____245 in
  let report uu____255 =
    let sorted1 =
      let uu____258 = FStar_ST.read errs in
      FStar_List.sortWith compare_issues uu____258 in
    FStar_List.iter print_issue sorted1; sorted1 in
  let clear1 uu____267 = FStar_ST.write errs [] in
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
  fun uu____289  ->
    let uu____290 =
      let uu____293 = FStar_ST.read current_handler in
      uu____293.eh_count_errors in
    uu____290 ()
let add_one: issue -> Prims.unit =
  fun issue  ->
    FStar_Util.atomically
      (fun uu____301  ->
         let uu____302 =
           let uu____305 = FStar_ST.read current_handler in
           uu____305.eh_add_one in
         uu____302 issue)
let add_many: issue Prims.list -> Prims.unit =
  fun issues  ->
    FStar_Util.atomically
      (fun uu____315  ->
         let uu____316 =
           let uu____319 = FStar_ST.read current_handler in
           uu____319.eh_add_one in
         FStar_List.iter uu____316 issues)
let report_all: Prims.unit -> issue Prims.list =
  fun uu____325  ->
    let uu____326 =
      let uu____330 = FStar_ST.read current_handler in uu____330.eh_report in
    uu____326 ()
let clear: Prims.unit -> Prims.unit =
  fun uu____335  ->
    let uu____336 =
      let uu____339 = FStar_ST.read current_handler in uu____339.eh_clear in
    uu____336 ()
let set_handler: error_handler -> Prims.unit =
  fun handler  ->
    let issues = report_all () in
    clear (); FStar_ST.write current_handler handler; add_many issues
let diag: FStar_Range.range -> Prims.string -> Prims.unit =
  fun r  ->
    fun msg  ->
      let uu____357 = FStar_Options.debug_any () in
      if uu____357 then add_one (mk_issue EInfo (Some r) msg) else ()
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
  let clear_prefix uu____434 = FStar_ST.write pfx None in
  let append_prefix s =
    let uu____442 = FStar_ST.read pfx in
    match uu____442 with
    | None  -> s
    | Some p -> Prims.strcat p (Prims.strcat ": " s) in
  { set_prefix; append_prefix; clear_prefix }
let add_errors: (Prims.string* FStar_Range.range) Prims.list -> Prims.unit =
  fun errs  ->
    FStar_Util.atomically
      (fun uu____458  ->
         FStar_List.iter
           (fun uu____465  ->
              match uu____465 with
              | (msg,r) ->
                  let uu____470 = message_prefix.append_prefix msg in
                  err r uu____470) errs)
let issue_of_exn: Prims.exn -> issue option =
  fun uu___59_474  ->
    match uu___59_474 with
    | Error (msg,r) ->
        let uu____478 =
          let uu____479 = message_prefix.append_prefix msg in
          mk_issue EError (Some r) uu____479 in
        Some uu____478
    | FStar_Util.NYI msg ->
        let uu____481 =
          let uu____482 = message_prefix.append_prefix msg in
          mk_issue ENotImplemented None uu____482 in
        Some uu____481
    | Err msg ->
        let uu____484 =
          let uu____485 = message_prefix.append_prefix msg in
          mk_issue EError None uu____485 in
        Some uu____484
    | uu____486 -> None
let err_exn: Prims.exn -> Prims.unit =
  fun exn  ->
    let uu____490 = issue_of_exn exn in
    match uu____490 with | Some issue -> add_one issue | None  -> raise exn
let handleable: Prims.exn -> Prims.bool =
  fun uu___60_495  ->
    match uu___60_495 with
    | Error uu____496 -> true
    | FStar_Util.NYI uu____499 -> true
    | Err uu____500 -> true
    | uu____501 -> false