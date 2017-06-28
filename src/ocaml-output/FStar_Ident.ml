
open Prims
open FStar_Pervasives
type ident =
{idText : Prims.string; idRange : FStar_Range.range}


let __proj__Mkident__item__idText : ident  ->  Prims.string = (fun projectee -> (match (projectee) with
| {idText = __fname__idText; idRange = __fname__idRange} -> begin
__fname__idText
end))


let __proj__Mkident__item__idRange : ident  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {idText = __fname__idText; idRange = __fname__idRange} -> begin
__fname__idRange
end))

type lident =
{ns : ident Prims.list; ident : ident; nsstr : Prims.string; str : Prims.string}


let __proj__Mklident__item__ns : lident  ->  ident Prims.list = (fun projectee -> (match (projectee) with
| {ns = __fname__ns; ident = __fname__ident; nsstr = __fname__nsstr; str = __fname__str} -> begin
__fname__ns
end))


let __proj__Mklident__item__ident : lident  ->  ident = (fun projectee -> (match (projectee) with
| {ns = __fname__ns; ident = __fname__ident; nsstr = __fname__nsstr; str = __fname__str} -> begin
__fname__ident
end))


let __proj__Mklident__item__nsstr : lident  ->  Prims.string = (fun projectee -> (match (projectee) with
| {ns = __fname__ns; ident = __fname__ident; nsstr = __fname__nsstr; str = __fname__str} -> begin
__fname__nsstr
end))


let __proj__Mklident__item__str : lident  ->  Prims.string = (fun projectee -> (match (projectee) with
| {ns = __fname__ns; ident = __fname__ident; nsstr = __fname__nsstr; str = __fname__str} -> begin
__fname__str
end))


type lid =
lident


let mk_ident : (Prims.string * FStar_Range.range)  ->  ident = (fun uu____81 -> (match (uu____81) with
| (text, range) -> begin
{idText = text; idRange = range}
end))


let reserved_prefix : Prims.string = "uu___"


let gen : FStar_Range.range  ->  ident = (

let x = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun r -> ((

let uu____94 = (

let uu____95 = (FStar_ST.read x)
in (uu____95 + (Prims.parse_int "1")))
in (FStar_ST.write x uu____94));
(

let uu____100 = (

let uu____103 = (

let uu____104 = (

let uu____105 = (FStar_ST.read x)
in (Prims.string_of_int uu____105))
in (Prims.strcat reserved_prefix uu____104))
in ((uu____103), (r)))
in (mk_ident uu____100));
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

let uu____155 = (FStar_List.map text_of_id ns)
in (FStar_All.pipe_right uu____155 text_of_path))
in {ns = ns; ident = id; nsstr = nsstr; str = (match ((nsstr = "")) with
| true -> begin
id.idText
end
| uu____158 -> begin
(Prims.strcat nsstr (Prims.strcat "." id.idText))
end)}))


let lid_of_ids : ident Prims.list  ->  lident = (fun ids -> (

let uu____165 = (FStar_Util.prefix ids)
in (match (uu____165) with
| (ns, id) -> begin
(lid_of_ns_and_id ns id)
end)))


let lid_of_str : Prims.string  ->  lident = (fun str -> (

let uu____177 = (FStar_List.map id_of_text (FStar_Util.split str "."))
in (lid_of_ids uu____177)))


let lid_of_path : Prims.string Prims.list  ->  FStar_Range.range  ->  lident = (fun path pos -> (

let ids = (FStar_List.map (fun s -> (mk_ident ((s), (pos)))) path)
in (lid_of_ids ids)))


let text_of_lid : lident  ->  Prims.string = (fun lid -> lid.str)


let lid_equals : lident  ->  lident  ->  Prims.bool = (fun l1 l2 -> (l1.str = l2.str))


let ident_equals : ident  ->  ident  ->  Prims.bool = (fun id1 id2 -> (id1.idText = id2.idText))


let range_of_lid : lid  ->  FStar_Range.range = (fun lid -> lid.ident.idRange)


let set_lid_range : lident  ->  FStar_Range.range  ->  lident = (fun l r -> (

let uu___47_225 = l
in {ns = uu___47_225.ns; ident = (

let uu___48_227 = l.ident
in {idText = uu___48_227.idText; idRange = r}); nsstr = uu___47_225.nsstr; str = uu___47_225.str}))


let lid_add_suffix : lident  ->  Prims.string  ->  lident = (fun l s -> (

let path = (path_of_lid l)
in (lid_of_path (FStar_List.append path ((s)::[])) (range_of_lid l))))


let string_of_lid : lident  ->  Prims.string = (fun lid -> (

let uu____242 = (path_of_lid lid)
in (text_of_path uu____242)))




