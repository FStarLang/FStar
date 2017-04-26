
open Prims
exception Err of (Prims.string)


let uu___is_Err : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Err (uu____6) -> begin
true
end
| uu____7 -> begin
false
end))


let __proj__Err__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| Err (uu____14) -> begin
uu____14
end))

exception Error of ((Prims.string * FStar_Range.range))


let uu___is_Error : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error (uu____22) -> begin
true
end
| uu____25 -> begin
false
end))


let __proj__Error__item__uu___ : Prims.exn  ->  (Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Error (uu____36) -> begin
uu____36
end))

exception Warning of ((Prims.string * FStar_Range.range))


let uu___is_Warning : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning (uu____46) -> begin
true
end
| uu____49 -> begin
false
end))


let __proj__Warning__item__uu___ : Prims.exn  ->  (Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Warning (uu____60) -> begin
uu____60
end))

exception Empty_frag


let uu___is_Empty_frag : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Empty_frag -> begin
true
end
| uu____66 -> begin
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
| uu____70 -> begin
false
end))


let uu___is_EInfo : issue_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EInfo -> begin
true
end
| uu____74 -> begin
false
end))


let uu___is_EWarning : issue_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EWarning -> begin
true
end
| uu____78 -> begin
false
end))


let uu___is_EError : issue_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EError -> begin
true
end
| uu____82 -> begin
false
end))

type issue =
{issue_message : Prims.string; issue_level : issue_level; issue_range : FStar_Range.range Prims.option}

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

let uu____170 = (match (issue.issue_range) with
| None -> begin
((""), (""))
end
| Some (r) -> begin
(

let uu____176 = (

let uu____177 = (FStar_Range.string_of_use_range r)
in (FStar_Util.format1 "%s: " uu____177))
in (

let uu____178 = (match ((r.FStar_Range.use_range = r.FStar_Range.def_range)) with
| true -> begin
""
end
| uu____179 -> begin
(

let uu____180 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 " (see also %s)" uu____180))
end)
in ((uu____176), (uu____178))))
end)
in (match (uu____170) with
| (range_str, see_also_str) -> begin
(FStar_Util.format4 "%s%s%s%s\n" range_str level_header issue.issue_message see_also_str)
end))))


let print_issue : issue  ->  Prims.unit = (fun issue -> (

let uu____186 = (format_issue issue)
in (FStar_Util.print_error uu____186)))


let compare_issues : issue  ->  issue  ->  Prims.int = (fun i1 i2 -> (match (((i1.issue_range), (i2.issue_range))) with
| (None, None) -> begin
(Prims.parse_int "0")
end
| (None, Some (uu____197)) -> begin
(~- ((Prims.parse_int "1")))
end
| (Some (uu____200), None) -> begin
(Prims.parse_int "1")
end
| (Some (r1), Some (r2)) -> begin
(FStar_Range.compare_use_range r1 r2)
end))


let default_handler : error_handler = (

let errs = (FStar_Util.mk_ref [])
in (

let add_one = (fun e -> (match (e.issue_level) with
| EError -> begin
(

let uu____216 = (

let uu____218 = (FStar_ST.read errs)
in (e)::uu____218)
in (FStar_ST.write errs uu____216))
end
| uu____226 -> begin
(print_issue e)
end))
in (

let count_errors = (fun uu____230 -> (

let uu____231 = (FStar_ST.read errs)
in (FStar_List.length uu____231)))
in (

let report = (fun uu____241 -> (

let sorted1 = (

let uu____244 = (FStar_ST.read errs)
in (FStar_List.sortWith compare_issues uu____244))
in ((FStar_List.iter print_issue sorted1);
sorted1;
)))
in (

let clear1 = (fun uu____253 -> (FStar_ST.write errs []))
in {eh_add_one = add_one; eh_count_errors = count_errors; eh_report = report; eh_clear = clear1})))))


let current_handler : error_handler FStar_ST.ref = (FStar_Util.mk_ref default_handler)


let mk_issue : issue_level  ->  FStar_Range.range Prims.option  ->  Prims.string  ->  issue = (fun level range msg -> {issue_message = msg; issue_level = level; issue_range = range})


let get_err_count : Prims.unit  ->  Prims.int = (fun uu____275 -> (

let uu____276 = (

let uu____279 = (FStar_ST.read current_handler)
in uu____279.eh_count_errors)
in (uu____276 ())))


let add_one : issue  ->  Prims.unit = (fun issue -> (FStar_Util.atomically (fun uu____285 -> (

let uu____286 = (

let uu____289 = (FStar_ST.read current_handler)
in uu____289.eh_add_one)
in (uu____286 issue)))))


let add_many : issue Prims.list  ->  Prims.unit = (fun issues -> (FStar_Util.atomically (fun uu____297 -> (

let uu____298 = (

let uu____301 = (FStar_ST.read current_handler)
in uu____301.eh_add_one)
in (FStar_List.iter uu____298 issues)))))


let report_all : Prims.unit  ->  issue Prims.list = (fun uu____307 -> (

let uu____308 = (

let uu____312 = (FStar_ST.read current_handler)
in uu____312.eh_report)
in (uu____308 ())))


let clear : Prims.unit  ->  Prims.unit = (fun uu____317 -> (

let uu____318 = (

let uu____321 = (FStar_ST.read current_handler)
in uu____321.eh_clear)
in (uu____318 ())))


let set_handler : error_handler  ->  Prims.unit = (fun handler -> (

let issues = (report_all ())
in ((clear ());
(FStar_ST.write current_handler handler);
(add_many issues);
)))


let diag : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (

let uu____339 = (FStar_Options.debug_any ())
in (match (uu____339) with
| true -> begin
(add_one (mk_issue EInfo (Some (r)) msg))
end
| uu____340 -> begin
()
end)))


let warn : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (add_one (mk_issue EWarning (Some (r)) msg)))


let err : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (add_one (mk_issue EError (Some (r)) msg)))

type error_message_prefix =
{set_prefix : Prims.string  ->  Prims.unit; append_prefix : Prims.string  ->  Prims.string; clear_prefix : Prims.unit  ->  Prims.unit}


let message_prefix : error_message_prefix = (

let pfx = (FStar_Util.mk_ref None)
in (

let set_prefix = (fun s -> (FStar_ST.write pfx (Some (s))))
in (

let clear_prefix = (fun uu____410 -> (FStar_ST.write pfx None))
in (

let append_prefix = (fun s -> (

let uu____418 = (FStar_ST.read pfx)
in (match (uu____418) with
| None -> begin
s
end
| Some (p) -> begin
(Prims.strcat p (Prims.strcat ": " s))
end)))
in {set_prefix = set_prefix; append_prefix = append_prefix; clear_prefix = clear_prefix}))))


let add_errors : (Prims.string * FStar_Range.range) Prims.list  ->  Prims.unit = (fun errs -> (FStar_Util.atomically (fun uu____433 -> (FStar_List.iter (fun uu____436 -> (match (uu____436) with
| (msg, r) -> begin
(

let uu____441 = (message_prefix.append_prefix msg)
in (err r uu____441))
end)) errs))))


let issue_of_exn : Prims.exn  ->  issue Prims.option = (fun uu___58_445 -> (match (uu___58_445) with
| Error (msg, r) -> begin
(

let uu____449 = (

let uu____450 = (message_prefix.append_prefix msg)
in (mk_issue EError (Some (r)) uu____450))
in Some (uu____449))
end
| FStar_Util.NYI (msg) -> begin
(

let uu____452 = (

let uu____453 = (message_prefix.append_prefix msg)
in (mk_issue ENotImplemented None uu____453))
in Some (uu____452))
end
| Err (msg) -> begin
(

let uu____455 = (

let uu____456 = (message_prefix.append_prefix msg)
in (mk_issue EError None uu____456))
in Some (uu____455))
end
| uu____457 -> begin
None
end))


let err_exn : Prims.exn  ->  Prims.unit = (fun exn -> (

let uu____461 = (issue_of_exn exn)
in (match (uu____461) with
| Some (issue) -> begin
(add_one issue)
end
| None -> begin
(Prims.raise exn)
end)))


let handleable : Prims.exn  ->  Prims.bool = (fun uu___59_466 -> (match (uu___59_466) with
| (Error (_)) | (FStar_Util.NYI (_)) | (Err (_)) -> begin
true
end
| uu____470 -> begin
false
end))




