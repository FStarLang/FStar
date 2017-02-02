
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
(

let uu____70 = (

let uu____71 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s : (Diagnostic) %s\n" uu____71 msg))
in (FStar_Util.print_string uu____70))
end
| uu____72 -> begin
()
end)))


let warn : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (

let uu____79 = (FStar_Range.string_of_range r)
in (FStar_Util.print2_error "%s: (Warning) %s\n" uu____79 msg)))


let num_errs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let verification_errs : (FStar_Range.range * Prims.string) Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

type error_message_prefix =
{set_prefix : Prims.string  ->  Prims.unit; append_prefix : Prims.string  ->  Prims.string; clear_prefix : Prims.unit  ->  Prims.unit}


let message_prefix : error_message_prefix = (

let pfx = (FStar_Util.mk_ref None)
in (

let set_prefix = (fun s -> (FStar_ST.write pfx (Some (s))))
in (

let clear_prefix = (fun uu____151 -> (FStar_ST.write pfx None))
in (

let append_prefix = (fun s -> (

let uu____159 = (FStar_ST.read pfx)
in (match (uu____159) with
| None -> begin
s
end
| Some (p) -> begin
(Prims.strcat p (Prims.strcat ": " s))
end)))
in {set_prefix = set_prefix; append_prefix = append_prefix; clear_prefix = clear_prefix}))))


let add_errors : (Prims.string * FStar_Range.range) Prims.list  ->  Prims.unit = (fun errs -> (

let errs = (FStar_All.pipe_right errs (FStar_List.map (fun uu____188 -> (match (uu____188) with
| (msg, r) -> begin
(

let uu____195 = (message_prefix.append_prefix msg)
in ((r), (uu____195)))
end))))
in (

let n_errs = (FStar_List.length errs)
in (FStar_Util.atomically (fun uu____200 -> ((

let uu____202 = (

let uu____206 = (FStar_ST.read verification_errs)
in (FStar_List.append errs uu____206))
in (FStar_ST.write verification_errs uu____202));
(

let uu____222 = (

let uu____223 = (FStar_ST.read num_errs)
in (uu____223 + n_errs))
in (FStar_ST.write num_errs uu____222));
))))))


let mk_error : Prims.string  ->  FStar_Range.range  ->  Prims.string = (fun msg r -> (match ((r.FStar_Range.use_range <> r.FStar_Range.def_range)) with
| true -> begin
(

let uu____236 = (FStar_Range.string_of_use_range r)
in (

let uu____237 = (FStar_Range.string_of_range r)
in (FStar_Util.format3 "%s: (Error) %s (see %s)\n" uu____236 msg uu____237)))
end
| uu____238 -> begin
(

let uu____239 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: (Error) %s\n" uu____239 msg))
end))


let report_all : Prims.unit  ->  Prims.nat = (fun uu____243 -> (

let all_errs = (FStar_Util.atomically (fun uu____251 -> (

let x = (FStar_ST.read verification_errs)
in ((FStar_ST.write verification_errs []);
x;
))))
in (

let all_errs = (FStar_List.sortWith (fun uu____275 uu____276 -> (match (((uu____275), (uu____276))) with
| ((r1, uu____286), (r2, uu____288)) -> begin
(FStar_Range.compare_use_range r1 r2)
end)) all_errs)
in ((FStar_All.pipe_right all_errs (FStar_List.iter (fun uu____299 -> (match (uu____299) with
| (r, msg) -> begin
(

let uu____304 = (mk_error msg r)
in (FStar_Util.print_error uu____304))
end))));
(FStar_List.length all_errs);
))))


let handle_err : Prims.bool  ->  Prims.exn  ->  Prims.unit = (fun warning e -> (match (e) with
| Error (msg, r) -> begin
(

let msg = (message_prefix.append_prefix msg)
in (

let uu____317 = (FStar_Range.string_of_range r)
in (FStar_Util.print3_error "%s : %s %s\n" uu____317 (match (warning) with
| true -> begin
"(Warning)"
end
| uu____318 -> begin
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
| uu____323 -> begin
(Prims.raise e)
end))


let handleable : Prims.exn  ->  Prims.bool = (fun uu___50_326 -> (match (uu___50_326) with
| (Error (_)) | (FStar_Util.NYI (_)) | (Err (_)) -> begin
true
end
| uu____330 -> begin
false
end))


let report : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> ((FStar_Util.incr num_errs);
(

let msg = (message_prefix.append_prefix msg)
in (

let uu____342 = (mk_error msg r)
in (FStar_Util.print_error uu____342)));
))


let get_err_count : Prims.unit  ->  Prims.int = (fun uu____345 -> (FStar_ST.read num_errs))




