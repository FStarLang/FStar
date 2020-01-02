
open Prims
open FStar_Pervasives
type counter =
{cid : Prims.string; total_time : Prims.int FStar_ST.ref; running : Prims.bool FStar_ST.ref; undercount : Prims.bool FStar_ST.ref}


let __proj__Mkcounter__item__cid : counter  ->  Prims.string = (fun projectee -> (match (projectee) with
| {cid = cid; total_time = total_time; running = running; undercount = undercount} -> begin
cid
end))


let __proj__Mkcounter__item__total_time : counter  ->  Prims.int FStar_ST.ref = (fun projectee -> (match (projectee) with
| {cid = cid; total_time = total_time; running = running; undercount = undercount} -> begin
total_time
end))


let __proj__Mkcounter__item__running : counter  ->  Prims.bool FStar_ST.ref = (fun projectee -> (match (projectee) with
| {cid = cid; total_time = total_time; running = running; undercount = undercount} -> begin
running
end))


let __proj__Mkcounter__item__undercount : counter  ->  Prims.bool FStar_ST.ref = (fun projectee -> (match (projectee) with
| {cid = cid; total_time = total_time; running = running; undercount = undercount} -> begin
undercount
end))


let new_counter : Prims.string  ->  counter = (fun cid -> (

let uu____171 = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let uu____177 = (FStar_Util.mk_ref false)
in (

let uu____183 = (FStar_Util.mk_ref false)
in {cid = cid; total_time = uu____171; running = uu____177; undercount = uu____183}))))


let all_counters : counter FStar_Util.smap = (FStar_Util.smap_create (Prims.parse_int "20"))


let create_or_lookup_counter : Prims.string  ->  counter = (fun cid -> (

let uu____201 = (FStar_Util.smap_try_find all_counters cid)
in (match (uu____201) with
| FStar_Pervasives_Native.Some (c) -> begin
c
end
| FStar_Pervasives_Native.None -> begin
(

let c = (new_counter cid)
in ((FStar_Util.smap_add all_counters cid c);
c;
))
end)))


let profile : 'a . (unit  ->  'a)  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  'a = (fun f module_name cid -> (

let uu____245 = (FStar_Options.profile_enabled module_name cid)
in (match (uu____245) with
| true -> begin
(

let c = (create_or_lookup_counter cid)
in (

let uu____249 = (FStar_ST.op_Bang c.running)
in (match (uu____249) with
| true -> begin
(f ())
end
| uu____273 -> begin
(FStar_All.try_with (fun uu___31_282 -> (match (()) with
| () -> begin
((FStar_ST.op_Colon_Equals c.running true);
(

let uu____306 = (FStar_Util.record_time f)
in (match (uu____306) with
| (res, elapsed) -> begin
((

let uu____317 = (

let uu____319 = (FStar_ST.op_Bang c.total_time)
in (uu____319 + elapsed))
in (FStar_ST.op_Colon_Equals c.total_time uu____317));
(FStar_ST.op_Colon_Equals c.running false);
res;
)
end));
)
end)) (fun uu___30_389 -> ((FStar_ST.op_Colon_Equals c.running false);
(FStar_ST.op_Colon_Equals c.undercount true);
(FStar_Exn.raise uu___30_389);
)))
end)))
end
| uu____436 -> begin
(f ())
end)))


let report_and_clear : Prims.string  ->  unit = (fun tag -> (

let ctrs = (FStar_Util.smap_fold all_counters (fun uu____454 v1 l -> (v1)::l) [])
in ((FStar_Util.smap_clear all_counters);
(

let ctrs1 = (FStar_Util.sort_with (fun c1 c2 -> (

let uu____470 = (FStar_ST.op_Bang c2.total_time)
in (

let uu____493 = (FStar_ST.op_Bang c1.total_time)
in (uu____470 - uu____493)))) ctrs)
in (FStar_All.pipe_right ctrs1 (FStar_List.iter (fun c -> (

let warn = (

let uu____524 = (FStar_ST.op_Bang c.running)
in (match (uu____524) with
| true -> begin
" (Warning, this counter is still running)"
end
| uu____550 -> begin
(

let uu____552 = (FStar_ST.op_Bang c.undercount)
in (match (uu____552) with
| true -> begin
" (Warning, some operations raised exceptions and we not accounted for)"
end
| uu____578 -> begin
""
end))
end))
in (

let uu____581 = (

let uu____583 = (FStar_ST.op_Bang c.total_time)
in (FStar_Util.string_of_int uu____583))
in (FStar_Util.print4 "%s, profiled %s:\t %s ms%s\n" tag c.cid uu____581 warn)))))));
)))




