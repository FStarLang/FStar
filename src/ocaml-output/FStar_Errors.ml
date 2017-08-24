
open Prims
open FStar_Pervasives
exception Err of (Prims.string)


let uu___is_Err : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Err (uu____7) -> begin
true
end
| uu____8 -> begin
false
end))


let __proj__Err__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| Err (uu____15) -> begin
uu____15
end))

exception Error of ((Prims.string * FStar_Range.range))


let uu___is_Error : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error (uu____24) -> begin
true
end
| uu____27 -> begin
false
end))


let __proj__Error__item__uu___ : Prims.exn  ->  (Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Error (uu____38) -> begin
uu____38
end))

exception Warning of ((Prims.string * FStar_Range.range))


let uu___is_Warning : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning (uu____49) -> begin
true
end
| uu____52 -> begin
false
end))


let __proj__Warning__item__uu___ : Prims.exn  ->  (Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Warning (uu____63) -> begin
uu____63
end))

exception Empty_frag


let uu___is_Empty_frag : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Empty_frag -> begin
true
end
| uu____69 -> begin
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
| uu____73 -> begin
false
end))


let uu___is_EInfo : issue_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EInfo -> begin
true
end
| uu____77 -> begin
false
end))


let uu___is_EWarning : issue_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EWarning -> begin
true
end
| uu____81 -> begin
false
end))


let uu___is_EError : issue_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EError -> begin
true
end
| uu____85 -> begin
false
end))

type issue =
{issue_message : Prims.string; issue_level : issue_level; issue_range : FStar_Range.range FStar_Pervasives_Native.option}

type error_handler =
{eh_add_one : issue  ->  Prims.unit; eh_count_errors : Prims.unit  ->  Prims.int; eh_report : Prims.unit  ->  issue Prims.list; eh_clear : Prims.unit  ->  Prims.unit}


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

let uu____184 = (match (issue.issue_range) with
| FStar_Pervasives_Native.None -> begin
((""), (""))
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____190 = (

let uu____191 = (FStar_Range.string_of_use_range r)
in (FStar_Util.format1 "%s: " uu____191))
in (

let uu____192 = (match ((r.FStar_Range.use_range = r.FStar_Range.def_range)) with
| true -> begin
""
end
| uu____193 -> begin
(

let uu____194 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 " (see also %s)" uu____194))
end)
in ((uu____190), (uu____192))))
end)
in (match (uu____184) with
| (range_str, see_also_str) -> begin
(FStar_Util.format4 "%s%s%s%s\n" range_str level_header issue.issue_message see_also_str)
end))))


let print_issue : issue  ->  Prims.unit = (fun issue -> (

let uu____200 = (format_issue issue)
in (FStar_Util.print_error uu____200)))


let compare_issues : issue  ->  issue  ->  Prims.int = (fun i1 i2 -> (match (((i1.issue_range), (i2.issue_range))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(Prims.parse_int "0")
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (uu____211)) -> begin
(~- ((Prims.parse_int "1")))
end
| (FStar_Pervasives_Native.Some (uu____214), FStar_Pervasives_Native.None) -> begin
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

let uu____230 = (

let uu____232 = (FStar_ST.read errs)
in (e)::uu____232)
in (FStar_ST.write errs uu____230))
end
| uu____240 -> begin
(print_issue e)
end))
in (

let count_errors = (fun uu____244 -> (

let uu____245 = (FStar_ST.read errs)
in (FStar_List.length uu____245)))
in (

let report = (fun uu____255 -> (

let sorted1 = (

let uu____258 = (FStar_ST.read errs)
in (FStar_List.sortWith compare_issues uu____258))
in ((FStar_List.iter print_issue sorted1);
sorted1;
)))
in (

let clear1 = (fun uu____267 -> (FStar_ST.write errs []))
in {eh_add_one = add_one; eh_count_errors = count_errors; eh_report = report; eh_clear = clear1})))))


let current_handler : error_handler FStar_ST.ref = (FStar_Util.mk_ref default_handler)


let mk_issue : issue_level  ->  FStar_Range.range FStar_Pervasives_Native.option  ->  Prims.string  ->  issue = (fun level range msg -> {issue_message = msg; issue_level = level; issue_range = range})


let get_err_count : Prims.unit  ->  Prims.int = (fun uu____289 -> (

let uu____290 = (

let uu____293 = (FStar_ST.read current_handler)
in uu____293.eh_count_errors)
in (uu____290 ())))


let add_one : issue  ->  Prims.unit = (fun issue -> (FStar_Util.atomically (fun uu____299 -> (

let uu____300 = (

let uu____303 = (FStar_ST.read current_handler)
in uu____303.eh_add_one)
in (uu____300 issue)))))


let add_many : issue Prims.list  ->  Prims.unit = (fun issues -> (FStar_Util.atomically (fun uu____311 -> (

let uu____312 = (

let uu____315 = (FStar_ST.read current_handler)
in uu____315.eh_add_one)
in (FStar_List.iter uu____312 issues)))))


let report_all : Prims.unit  ->  issue Prims.list = (fun uu____321 -> (

let uu____322 = (

let uu____326 = (FStar_ST.read current_handler)
in uu____326.eh_report)
in (uu____322 ())))


let clear : Prims.unit  ->  Prims.unit = (fun uu____331 -> (

let uu____332 = (

let uu____335 = (FStar_ST.read current_handler)
in uu____335.eh_clear)
in (uu____332 ())))


let set_handler : error_handler  ->  Prims.unit = (fun handler -> (

let issues = (report_all ())
in ((clear ());
(FStar_ST.write current_handler handler);
(add_many issues);
)))


let diag : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (

let uu____353 = (FStar_Options.debug_any ())
in (match (uu____353) with
| true -> begin
(add_one (mk_issue EInfo (FStar_Pervasives_Native.Some (r)) msg))
end
| uu____354 -> begin
()
end)))


let warn : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (add_one (mk_issue EWarning (FStar_Pervasives_Native.Some (r)) msg)))


let err : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (add_one (mk_issue EError (FStar_Pervasives_Native.Some (r)) msg)))

type error_message_prefix =
{set_prefix : Prims.string  ->  Prims.unit; append_prefix : Prims.string  ->  Prims.string; clear_prefix : Prims.unit  ->  Prims.unit}


let message_prefix : error_message_prefix = (

let pfx = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let set_prefix = (fun s -> (FStar_ST.write pfx (FStar_Pervasives_Native.Some (s))))
in (

let clear_prefix = (fun uu____430 -> (FStar_ST.write pfx FStar_Pervasives_Native.None))
in (

let append_prefix = (fun s -> (

let uu____438 = (FStar_ST.read pfx)
in (match (uu____438) with
| FStar_Pervasives_Native.None -> begin
s
end
| FStar_Pervasives_Native.Some (p) -> begin
(Prims.strcat p (Prims.strcat ": " s))
end)))
in {set_prefix = set_prefix; append_prefix = append_prefix; clear_prefix = clear_prefix}))))


let add_errors : (Prims.string * FStar_Range.range) Prims.list  ->  Prims.unit = (fun errs -> (FStar_Util.atomically (fun uu____453 -> (FStar_List.iter (fun uu____456 -> (match (uu____456) with
| (msg, r) -> begin
(

let uu____461 = (message_prefix.append_prefix msg)
in (err r uu____461))
end)) errs))))


let issue_of_exn : Prims.exn  ->  issue FStar_Pervasives_Native.option = (fun uu___59_465 -> (match (uu___59_465) with
| Error (msg, r) -> begin
(

let uu____469 = (

let uu____470 = (message_prefix.append_prefix msg)
in (mk_issue EError (FStar_Pervasives_Native.Some (r)) uu____470))
in FStar_Pervasives_Native.Some (uu____469))
end
| FStar_Util.NYI (msg) -> begin
(

let uu____472 = (

let uu____473 = (message_prefix.append_prefix msg)
in (mk_issue ENotImplemented FStar_Pervasives_Native.None uu____473))
in FStar_Pervasives_Native.Some (uu____472))
end
| Err (msg) -> begin
(

let uu____475 = (

let uu____476 = (message_prefix.append_prefix msg)
in (mk_issue EError FStar_Pervasives_Native.None uu____476))
in FStar_Pervasives_Native.Some (uu____475))
end
| uu____477 -> begin
FStar_Pervasives_Native.None
end))


let err_exn : Prims.exn  ->  Prims.unit = (fun exn -> (

let uu____481 = (issue_of_exn exn)
in (match (uu____481) with
| FStar_Pervasives_Native.Some (issue) -> begin
(add_one issue)
end
| FStar_Pervasives_Native.None -> begin
(FStar_Pervasives.raise exn)
end)))


let handleable : Prims.exn  ->  Prims.bool = (fun uu___60_486 -> (match (uu___60_486) with
| Error (uu____487) -> begin
true
end
| FStar_Util.NYI (uu____490) -> begin
true
end
| Err (uu____491) -> begin
true
end
| uu____492 -> begin
false
end))




