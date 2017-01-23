
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


let diag : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (

let uu____69 = (FStar_Options.debug_any ())
in (match (uu____69) with
| true -> begin
(FStar_Util.print_string (let _0_104 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s : (Diagnostic) %s\n" _0_104 msg)))
end
| uu____70 -> begin
()
end)))


let warn : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (let _0_105 = (FStar_Range.string_of_range r)
in (FStar_Util.print2_error "%s: (Warning) %s\n" _0_105 msg)))


let num_errs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let verification_errs : (FStar_Range.range * Prims.string) Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

type error_message_prefix =
{set_prefix : Prims.string  ->  Prims.unit; append_prefix : Prims.string  ->  Prims.string; clear_prefix : Prims.unit  ->  Prims.unit}


let message_prefix : error_message_prefix = (

let pfx = (FStar_Util.mk_ref None)
in (

let set_prefix = (fun s -> (FStar_ST.write pfx (Some (s))))
in (

let clear_prefix = (fun uu____148 -> (FStar_ST.write pfx None))
in (

let append_prefix = (fun s -> (

let uu____156 = (FStar_ST.read pfx)
in (match (uu____156) with
| None -> begin
s
end
| Some (p) -> begin
(Prims.strcat p (Prims.strcat ": " s))
end)))
in {set_prefix = set_prefix; append_prefix = append_prefix; clear_prefix = clear_prefix}))))


let add_errors : (Prims.string * FStar_Range.range) Prims.list  ->  Prims.unit = (fun errs -> (

let errs = (FStar_All.pipe_right errs (FStar_List.map (fun uu____185 -> (match (uu____185) with
| (msg, r) -> begin
(let _0_106 = (message_prefix.append_prefix msg)
in ((r), (_0_106)))
end))))
in (

let n_errs = (FStar_List.length errs)
in (FStar_Util.atomically (fun uu____196 -> ((let _0_108 = (let _0_107 = (FStar_ST.read verification_errs)
in (FStar_List.append errs _0_107))
in (FStar_ST.write verification_errs _0_108));
(let _0_110 = (let _0_109 = (FStar_ST.read num_errs)
in (_0_109 + n_errs))
in (FStar_ST.write num_errs _0_110));
))))))


let mk_error : Prims.string  ->  FStar_Range.range  ->  Prims.string = (fun msg r -> (match ((r.FStar_Range.use_range <> r.FStar_Range.def_range)) with
| true -> begin
(let _0_112 = (FStar_Range.string_of_use_range r)
in (let _0_111 = (FStar_Range.string_of_range r)
in (FStar_Util.format3 "%s: (Error) %s (see %s)\n" _0_112 msg _0_111)))
end
| uu____222 -> begin
(let _0_113 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: (Error) %s\n" _0_113 msg))
end))


let report_all : Prims.unit  ->  Prims.nat = (fun uu____226 -> (

let all_errs = (FStar_Util.atomically (fun uu____234 -> (

let x = (FStar_ST.read verification_errs)
in ((FStar_ST.write verification_errs []);
x;
))))
in (

let all_errs = (FStar_List.sortWith (fun uu____258 uu____259 -> (match (((uu____258), (uu____259))) with
| ((r1, uu____269), (r2, uu____271)) -> begin
(FStar_Range.compare_use_range r1 r2)
end)) all_errs)
in ((FStar_All.pipe_right all_errs (FStar_List.iter (fun uu____282 -> (match (uu____282) with
| (r, msg) -> begin
(FStar_Util.print_error (mk_error msg r))
end))));
(FStar_List.length all_errs);
))))


let handle_err : Prims.bool  ->  Prims.exn  ->  Prims.unit = (fun warning e -> (match (e) with
| Error (msg, r) -> begin
(

let msg = (message_prefix.append_prefix msg)
in (let _0_114 = (FStar_Range.string_of_range r)
in (FStar_Util.print3_error "%s : %s %s\n" _0_114 (match (warning) with
| true -> begin
"(Warning)"
end
| uu____299 -> begin
"(Error)"
end) msg)))
end
| FStar_Util.NYI (msg) -> begin
(

let msg = (message_prefix.append_prefix msg)
in (FStar_Util.print1_error "Feature not yet implemented: %s" msg))
end
| Err (msg) -> begin
(

let msg = (message_prefix.append_prefix msg)
in (FStar_Util.print1_error "Error: %s" msg))
end
| uu____304 -> begin
(Prims.raise e)
end))


let handleable : Prims.exn  ->  Prims.bool = (fun uu___50_307 -> (match (uu___50_307) with
| (Error (_)) | (FStar_Util.NYI (_)) | (Err (_)) -> begin
true
end
| uu____311 -> begin
false
end))


let report : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> ((FStar_Util.incr num_errs);
(

let msg = (message_prefix.append_prefix msg)
in (FStar_Util.print_error (mk_error msg r)));
))


let get_err_count : Prims.unit  ->  Prims.int = (fun uu____325 -> (FStar_ST.read num_errs))




