
open Prims
type ident =
{idText : Prims.string; idRange : FStar_Range.range}

type lident =
{ns : ident Prims.list; ident : ident; nsstr : Prims.string; str : Prims.string}


type lid =
lident


let mk_ident : (Prims.string * FStar_Range.range)  ->  ident = (fun uu____50 -> (match (uu____50) with
| (text, range) -> begin
{idText = text; idRange = range}
end))


let reserved_prefix : Prims.string = "uu___"


let gen : FStar_Range.range  ->  ident = (

let x = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun r -> ((

let uu____62 = (

let uu____63 = (FStar_ST.read x)
in (uu____63 + (Prims.parse_int "1")))
in (FStar_ST.write x uu____62));
(

let uu____68 = (

let uu____71 = (

let uu____72 = (

let uu____73 = (FStar_ST.read x)
in (Prims.string_of_int uu____73))
in (Prims.strcat reserved_prefix uu____72))
in ((uu____71), (r)))
in (mk_ident uu____68));
)))


let id_of_text : Prims.string  ->  ident = (fun str -> (mk_ident ((str), (FStar_Range.dummyRange))))


let text_of_id : ident  ->  Prims.string = (fun id -> id.idText)


let text_of_path : Prims.string Prims.list  ->  Prims.string = (fun path -> (FStar_Util.concat_l "." path))


let path_of_text : Prims.string  ->  Prims.string Prims.list = (fun text -> (FStar_String.split (('.')::[]) text))


let path_of_ns : ident Prims.list  ->  Prims.string Prims.list = (fun ns -> (FStar_List.map text_of_id ns))


let path_of_lid : lident  ->  Prims.string Prims.list = (fun lid -> (FStar_List.map text_of_id (FStar_List.append lid.ns ((lid.ident)::[]))))


let ids_of_lid : lident  ->  ident Prims.list = (fun lid -> (FStar_List.append lid.ns ((lid.ident)::[])))


let lid_of_ns_and_id : ident Prims.list  ->  ident  ->  lident = (fun ns id -> (

let nsstr = (

let uu____114 = (FStar_List.map text_of_id ns)
in (FStar_All.pipe_right uu____114 text_of_path))
in {ns = ns; ident = id; nsstr = nsstr; str = (match ((nsstr = "")) with
| true -> begin
id.idText
end
| uu____117 -> begin
(Prims.strcat nsstr (Prims.strcat "." id.idText))
end)}))


let lid_of_ids : ident Prims.list  ->  lident = (fun ids -> (

let uu____123 = (FStar_Util.prefix ids)
in (match (uu____123) with
| (ns, id) -> begin
(lid_of_ns_and_id ns id)
end)))


let lid_of_path : Prims.string Prims.list  ->  FStar_Range.range  ->  lident = (fun path pos -> (

let ids = (FStar_List.map (fun s -> (mk_ident ((s), (pos)))) path)
in (lid_of_ids ids)))


let text_of_lid : lident  ->  Prims.string = (fun lid -> lid.str)


let lid_equals : lident  ->  lident  ->  Prims.bool = (fun l1 l2 -> (l1.str = l2.str))


let ident_equals : ident  ->  ident  ->  Prims.bool = (fun id1 id2 -> (id1.idText = id2.idText))


let range_of_lid : lid  ->  FStar_Range.range = (fun lid -> lid.ident.idRange)


let set_lid_range : lident  ->  FStar_Range.range  ->  lident = (fun l r -> (

let uu___45_166 = l
in {ns = uu___45_166.ns; ident = (

let uu___46_167 = l.ident
in {idText = uu___46_167.idText; idRange = r}); nsstr = uu___45_166.nsstr; str = uu___45_166.str}))


let lid_add_suffix : lident  ->  Prims.string  ->  lident = (fun l s -> (

let path = (path_of_lid l)
in (lid_of_path (FStar_List.append path ((s)::[])) (range_of_lid l))))


let string_of_lid : lident  ->  Prims.string = (fun lid -> (

let uu____179 = (path_of_lid lid)
in (text_of_path uu____179)))




