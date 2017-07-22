
open Prims
open FStar_Pervasives
exception Err of (Prims.string)


let uu___is_Err : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Err (uu____8) -> begin
true
end
| uu____9 -> begin
false
end))


let __proj__Err__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| Err (uu____17) -> begin
uu____17
end))

exception Error of ((Prims.string * FStar_Range.range))


let uu___is_Error : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error (uu____29) -> begin
true
end
| uu____34 -> begin
false
end))


let __proj__Error__item__uu___ : Prims.exn  ->  (Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Error (uu____50) -> begin
uu____50
end))

exception Warning of ((Prims.string * FStar_Range.range))


let uu___is_Warning : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning (uu____66) -> begin
true
end
| uu____71 -> begin
false
end))


let __proj__Warning__item__uu___ : Prims.exn  ->  (Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Warning (uu____87) -> begin
uu____87
end))

exception Empty_frag


let uu___is_Empty_frag : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Empty_frag -> begin
true
end
| uu____96 -> begin
false
end))

type issue_level =
| ENotImplemented
| EInfo
| EWarning
| EError


let uu___is_ENotImplemented : issue_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ENotImplemented -> begin
true
end
| uu____101 -> begin
false
end))


let uu___is_EInfo : issue_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EInfo -> begin
true
end
| uu____106 -> begin
false
end))


let uu___is_EWarning : issue_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EWarning -> begin
true
end
| uu____111 -> begin
false
end))


let uu___is_EError : issue_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EError -> begin
true
end
| uu____116 -> begin
false
end))

type issue =
{issue_message : Prims.string; issue_level : issue_level; issue_range : FStar_Range.range FStar_Pervasives_Native.option}


let __proj__Mkissue__item__issue_message : issue  ->  Prims.string = (fun projectee -> (match (projectee) with
| {issue_message = __fname__issue_message; issue_level = __fname__issue_level; issue_range = __fname__issue_range} -> begin
__fname__issue_message
end))


let __proj__Mkissue__item__issue_level : issue  ->  issue_level = (fun projectee -> (match (projectee) with
| {issue_message = __fname__issue_message; issue_level = __fname__issue_level; issue_range = __fname__issue_range} -> begin
__fname__issue_level
end))


let __proj__Mkissue__item__issue_range : issue  ->  FStar_Range.range FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {issue_message = __fname__issue_message; issue_level = __fname__issue_level; issue_range = __fname__issue_range} -> begin
__fname__issue_range
end))

type error_handler =
{eh_add_one : issue  ->  Prims.unit; eh_count_errors : Prims.unit  ->  Prims.int; eh_report : Prims.unit  ->  issue Prims.list; eh_clear : Prims.unit  ->  Prims.unit}


let __proj__Mkerror_handler__item__eh_add_one : error_handler  ->  issue  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {eh_add_one = __fname__eh_add_one; eh_count_errors = __fname__eh_count_errors; eh_report = __fname__eh_report; eh_clear = __fname__eh_clear} -> begin
__fname__eh_add_one
end))


let __proj__Mkerror_handler__item__eh_count_errors : error_handler  ->  Prims.unit  ->  Prims.int = (fun projectee -> (match (projectee) with
| {eh_add_one = __fname__eh_add_one; eh_count_errors = __fname__eh_count_errors; eh_report = __fname__eh_report; eh_clear = __fname__eh_clear} -> begin
__fname__eh_count_errors
end))


let __proj__Mkerror_handler__item__eh_report : error_handler  ->  Prims.unit  ->  issue Prims.list = (fun projectee -> (match (projectee) with
| {eh_add_one = __fname__eh_add_one; eh_count_errors = __fname__eh_count_errors; eh_report = __fname__eh_report; eh_clear = __fname__eh_clear} -> begin
__fname__eh_report
end))


let __proj__Mkerror_handler__item__eh_clear : error_handler  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {eh_add_one = __fname__eh_add_one; eh_count_errors = __fname__eh_count_errors; eh_report = __fname__eh_report; eh_clear = __fname__eh_clear} -> begin
__fname__eh_clear
end))


let format_issue : issue  ->  Prims.string = (fun issue -> (

let level_header = (match (issue.issue_level) with
| EInfo -> begin
"(Info) "
end
| EWarning -> begin
"(Warning) "
end
| EError -> begin
"(Error) "
end
| ENotImplemented -> begin
"Feature not yet implemented: "
end)
in (

let uu____297 = (match (issue.issue_range) with
| FStar_Pervasives_Native.None -> begin
((""), (""))
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____307 = (

let uu____308 = (FStar_Range.string_of_use_range r)
in (FStar_Util.format1 "%s: " uu____308))
in (

let uu____309 = (match ((r.FStar_Range.use_range = r.FStar_Range.def_range)) with
| true -> begin
""
end
| uu____310 -> begin
(

let uu____311 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 " (see also %s)" uu____311))
end)
in ((uu____307), (uu____309))))
end)
in (match (uu____297) with
| (range_str, see_also_str) -> begin
(FStar_Util.format4 "%s%s%s%s\n" range_str level_header issue.issue_message see_also_str)
end))))


let print_issue : issue  ->  Prims.unit = (fun issue -> (

let uu____318 = (format_issue issue)
in (FStar_Util.print_error uu____318)))


let compare_issues : issue  ->  issue  ->  Prims.int = (fun i1 i2 -> (match (((i1.issue_range), (i2.issue_range))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(Prims.parse_int "0")
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (uu____335)) -> begin
(~- ((Prims.parse_int "1")))
end
| (FStar_Pervasives_Native.Some (uu____340), FStar_Pervasives_Native.None) -> begin
(Prims.parse_int "1")
end
| (FStar_Pervasives_Native.Some (r1), FStar_Pervasives_Native.Some (r2)) -> begin
(FStar_Range.compare_use_range r1 r2)
end))


let default_handler : error_handler = (

let errs = (FStar_Util.mk_ref [])
in (

let add_one = (fun e -> (match (e.issue_level) with
| EError -> begin
(

let uu____362 = (

let uu____365 = (FStar_ST.read errs)
in (e)::uu____365)
in (FStar_ST.write errs uu____362))
end
| uu____376 -> begin
(print_issue e)
end))
in (

let count_errors = (fun uu____380 -> (

let uu____381 = (FStar_ST.read errs)
in (FStar_List.length uu____381)))
in (

let report = (fun uu____393 -> (

let sorted1 = (

let uu____397 = (FStar_ST.read errs)
in (FStar_List.sortWith compare_issues uu____397))
in ((FStar_List.iter print_issue sorted1);
sorted1;
)))
in (

let clear1 = (fun uu____408 -> (FStar_ST.write errs []))
in {eh_add_one = add_one; eh_count_errors = count_errors; eh_report = report; eh_clear = clear1})))))


let current_handler : error_handler FStar_ST.ref = (FStar_Util.mk_ref default_handler)


let mk_issue : issue_level  ->  FStar_Range.range FStar_Pervasives_Native.option  ->  Prims.string  ->  issue = (fun level range msg -> {issue_message = msg; issue_level = level; issue_range = range})


let get_err_count : Prims.unit  ->  Prims.int = (fun uu____439 -> (

let uu____440 = (

let uu____443 = (FStar_ST.read current_handler)
in uu____443.eh_count_errors)
in (uu____440 ())))


let add_one : issue  ->  Prims.unit = (fun issue -> (FStar_Util.atomically (fun uu____450 -> (

let uu____451 = (

let uu____454 = (FStar_ST.read current_handler)
in uu____454.eh_add_one)
in (uu____451 issue)))))


let add_many : issue Prims.list  ->  Prims.unit = (fun issues -> (FStar_Util.atomically (fun uu____465 -> (

let uu____466 = (

let uu____469 = (FStar_ST.read current_handler)
in uu____469.eh_add_one)
in (FStar_List.iter uu____466 issues)))))


let report_all : Prims.unit  ->  issue Prims.list = (fun uu____475 -> (

let uu____476 = (

let uu____481 = (FStar_ST.read current_handler)
in uu____481.eh_report)
in (uu____476 ())))


let clear : Prims.unit  ->  Prims.unit = (fun uu____485 -> (

let uu____486 = (

let uu____489 = (FStar_ST.read current_handler)
in uu____489.eh_clear)
in (uu____486 ())))


let set_handler : error_handler  ->  Prims.unit = (fun handler -> (

let issues = (report_all ())
in ((clear ());
(FStar_ST.write current_handler handler);
(add_many issues);
)))


let diag : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (

let uu____507 = (FStar_Options.debug_any ())
in (match (uu____507) with
| true -> begin
(add_one (mk_issue EInfo (FStar_Pervasives_Native.Some (r)) msg))
end
| uu____508 -> begin
()
end)))


let warn : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (add_one (mk_issue EWarning (FStar_Pervasives_Native.Some (r)) msg)))


let err : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (add_one (mk_issue EError (FStar_Pervasives_Native.Some (r)) msg)))

type error_message_prefix =
{set_prefix : Prims.string  ->  Prims.unit; append_prefix : Prims.string  ->  Prims.string; clear_prefix : Prims.unit  ->  Prims.unit}


let __proj__Mkerror_message_prefix__item__set_prefix : error_message_prefix  ->  Prims.string  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {set_prefix = __fname__set_prefix; append_prefix = __fname__append_prefix; clear_prefix = __fname__clear_prefix} -> begin
__fname__set_prefix
end))


let __proj__Mkerror_message_prefix__item__append_prefix : error_message_prefix  ->  Prims.string  ->  Prims.string = (fun projectee -> (match (projectee) with
| {set_prefix = __fname__set_prefix; append_prefix = __fname__append_prefix; clear_prefix = __fname__clear_prefix} -> begin
__fname__append_prefix
end))


let __proj__Mkerror_message_prefix__item__clear_prefix : error_message_prefix  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {set_prefix = __fname__set_prefix; append_prefix = __fname__append_prefix; clear_prefix = __fname__clear_prefix} -> begin
__fname__clear_prefix
end))


let message_prefix : error_message_prefix = (

let pfx = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let set_prefix = (fun s -> (FStar_ST.write pfx (FStar_Pervasives_Native.Some (s))))
in (

let clear_prefix = (fun uu____621 -> (FStar_ST.write pfx FStar_Pervasives_Native.None))
in (

let append_prefix = (fun s -> (

let uu____630 = (FStar_ST.read pfx)
in (match (uu____630) with
| FStar_Pervasives_Native.None -> begin
s
end
| FStar_Pervasives_Native.Some (p) -> begin
(Prims.strcat p (Prims.strcat ": " s))
end)))
in {set_prefix = set_prefix; append_prefix = append_prefix; clear_prefix = clear_prefix}))))


let add_errors : (Prims.string * FStar_Range.range) Prims.list  ->  Prims.unit = (fun errs -> (FStar_Util.atomically (fun uu____655 -> (FStar_List.iter (fun uu____664 -> (match (uu____664) with
| (msg, r) -> begin
(

let uu____671 = (message_prefix.append_prefix msg)
in (err r uu____671))
end)) errs))))


let issue_of_exn : Prims.exn  ->  issue FStar_Pervasives_Native.option = (fun uu___59_677 -> (match (uu___59_677) with
| Error (msg, r) -> begin
(

let uu____682 = (

let uu____683 = (message_prefix.append_prefix msg)
in (mk_issue EError (FStar_Pervasives_Native.Some (r)) uu____683))
in FStar_Pervasives_Native.Some (uu____682))
end
| FStar_Util.NYI (msg) -> begin
(

let uu____685 = (

let uu____686 = (message_prefix.append_prefix msg)
in (mk_issue ENotImplemented FStar_Pervasives_Native.None uu____686))
in FStar_Pervasives_Native.Some (uu____685))
end
| Err (msg) -> begin
(

let uu____688 = (

let uu____689 = (message_prefix.append_prefix msg)
in (mk_issue EError FStar_Pervasives_Native.None uu____689))
in FStar_Pervasives_Native.Some (uu____688))
end
| uu____690 -> begin
FStar_Pervasives_Native.None
end))


let err_exn : Prims.exn  ->  Prims.unit = (fun exn -> (

let uu____695 = (issue_of_exn exn)
in (match (uu____695) with
| FStar_Pervasives_Native.Some (issue) -> begin
(add_one issue)
end
| FStar_Pervasives_Native.None -> begin
(FStar_Pervasives.raise exn)
end)))


let handleable : Prims.exn  ->  Prims.bool = (fun uu___60_702 -> (match (uu___60_702) with
| Error (uu____703) -> begin
true
end
| FStar_Util.NYI (uu____708) -> begin
true
end
| Err (uu____709) -> begin
true
end
| uu____710 -> begin
false
end))




