
open Prims

exception Err of (Prims.string)


let is_Err = (fun _discr_ -> (match (_discr_) with
| Err (_) -> begin
true
end
| _ -> begin
false
end))


let ___Err____0 = (fun projectee -> (match (projectee) with
| Err (_28_3) -> begin
_28_3
end))


exception Error of ((Prims.string * FStar_Range.range))


let is_Error = (fun _discr_ -> (match (_discr_) with
| Error (_) -> begin
true
end
| _ -> begin
false
end))


let ___Error____0 = (fun projectee -> (match (projectee) with
| Error (_28_5) -> begin
_28_5
end))


exception Warning of ((Prims.string * FStar_Range.range))


let is_Warning = (fun _discr_ -> (match (_discr_) with
| Warning (_) -> begin
true
end
| _ -> begin
false
end))


let ___Warning____0 = (fun projectee -> (match (projectee) with
| Warning (_28_7) -> begin
_28_7
end))


let diag : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> if (FStar_Options.debug_any ()) then begin
(let _129_21 = (let _129_20 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s : (Diagnostic) %s\n" _129_20 msg))
in (FStar_Util.print_string _129_21))
end else begin
()
end)


let warn : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (let _129_26 = (FStar_Range.string_of_range r)
in (FStar_Util.print2_error "%s: (Warning) %s\n" _129_26 msg)))


let num_errs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let verification_errs : (FStar_Range.range * Prims.string) Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


type error_message_prefix =
{set_prefix : Prims.string  ->  Prims.unit; append_prefix : Prims.string  ->  Prims.string; clear_prefix : Prims.unit  ->  Prims.unit}


let is_Mkerror_message_prefix : error_message_prefix  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkerror_message_prefix"))))


let message_prefix : error_message_prefix = (

let pfx = (FStar_Util.mk_ref None)
in (

let set_prefix = (fun s -> (FStar_ST.op_Colon_Equals pfx (Some (s))))
in (

let clear_prefix = (fun _28_20 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals pfx None)
end))
in (

let append_prefix = (fun s -> (match ((FStar_ST.read pfx)) with
| None -> begin
s
end
| Some (p) -> begin
(Prims.strcat p (Prims.strcat ": " s))
end))
in {set_prefix = set_prefix; append_prefix = append_prefix; clear_prefix = clear_prefix}))))


let add_errors : (Prims.string * FStar_Range.range) Prims.list  ->  Prims.unit = (fun errs -> (

let errs = (FStar_All.pipe_right errs (FStar_List.map (fun _28_29 -> (match (_28_29) with
| (msg, r) -> begin
(let _129_64 = (message_prefix.append_prefix msg)
in ((r), (_129_64)))
end))))
in (

let n_errs = (FStar_List.length errs)
in (FStar_Util.atomically (fun _28_32 -> (match (()) with
| () -> begin
(

let _28_33 = (let _129_67 = (let _129_66 = (FStar_ST.read verification_errs)
in (FStar_List.append errs _129_66))
in (FStar_ST.op_Colon_Equals verification_errs _129_67))
in (let _129_68 = ((FStar_ST.read num_errs) + n_errs)
in (FStar_ST.op_Colon_Equals num_errs _129_68)))
end))))))


let mk_error : Prims.string  ->  FStar_Range.range  ->  Prims.string = (fun msg r -> if (r.FStar_Range.use_range <> r.FStar_Range.def_range) then begin
(let _129_74 = (FStar_Range.string_of_use_range r)
in (let _129_73 = (FStar_Range.string_of_range r)
in (FStar_Util.format3 "%s: (Error) %s (see %s)\n" _129_74 msg _129_73)))
end else begin
(let _129_75 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: (Error) %s\n" _129_75 msg))
end)


let report_all : Prims.unit  ->  Prims.int = (fun _28_37 -> (match (()) with
| () -> begin
(

let all_errs = (FStar_Util.atomically (fun _28_38 -> (match (()) with
| () -> begin
(

let x = (FStar_ST.read verification_errs)
in (

let _28_40 = (FStar_ST.op_Colon_Equals verification_errs [])
in x))
end)))
in (

let all_errs = (FStar_List.sortWith (fun _28_46 _28_50 -> (match (((_28_46), (_28_50))) with
| ((r1, _28_45), (r2, _28_49)) -> begin
(FStar_Range.compare_use_range r1 r2)
end)) all_errs)
in (

let _28_55 = (FStar_All.pipe_right all_errs (FStar_List.iter (fun _28_54 -> (match (_28_54) with
| (r, msg) -> begin
(let _129_82 = (mk_error msg r)
in (FStar_Util.print_error _129_82))
end))))
in (FStar_List.length all_errs))))
end))


let handle_err : Prims.bool  ->  Prims.exn  ->  Prims.unit = (fun warning e -> (match (e) with
| Error (msg, r) -> begin
(

let msg = (message_prefix.append_prefix msg)
in (let _129_87 = (FStar_Range.string_of_range r)
in (FStar_Util.print3_error "%s : %s %s\n" _129_87 (if warning then begin
"(Warning)"
end else begin
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
| _28_71 -> begin
(Prims.raise e)
end))


let handleable : Prims.exn  ->  Prims.bool = (fun _28_1 -> (match (_28_1) with
| (Error (_)) | (FStar_Util.NYI (_)) | (Err (_)) -> begin
true
end
| _28_83 -> begin
false
end))


let report : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (

let _28_86 = (FStar_Util.incr num_errs)
in (

let msg = (message_prefix.append_prefix msg)
in (let _129_94 = (mk_error msg r)
in (FStar_Util.print_error _129_94)))))


let get_err_count : Prims.unit  ->  Prims.int = (fun _28_89 -> (match (()) with
| () -> begin
(FStar_ST.read num_errs)
end))




