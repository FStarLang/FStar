
open Prims
type ident =
{idText : Prims.string; idRange : FStar_Range.range}

let is_Mkident = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkident"))))

type lident =
{ns : ident Prims.list; ident : ident; nsstr : Prims.string; str : Prims.string}

let is_Mklident = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mklident"))))

type lid =
lident

let mk_ident = (fun _22_11 -> (match (_22_11) with
| (text, range) -> begin
{idText = text; idRange = range}
end))

let gen = (let x = (FStar_ST.alloc 0)
in (fun r -> (let _22_14 = (let _113_25 = ((FStar_ST.read x) + 1)
in (FStar_ST.op_Colon_Equals x _113_25))
in (let _113_29 = (let _113_28 = (let _113_27 = (let _113_26 = (FStar_ST.read x)
in (Prims.string_of_int _113_26))
in (Prims.strcat "@x_" _113_27))
in (_113_28, r))
in (mk_ident _113_29)))))

let id_of_text = (fun str -> (mk_ident (str, FStar_Range.dummyRange)))

let text_of_id = (fun id -> id.idText)

let text_of_path = (fun path -> (FStar_Util.concat_l "." path))

let path_of_text = (fun text -> (FStar_String.split (('.')::[]) text))

let path_of_ns = (fun ns -> (FStar_List.map text_of_id ns))

let path_of_lid = (fun lid -> (FStar_List.map text_of_id (FStar_List.append lid.ns ((lid.ident)::[]))))

let ids_of_lid = (fun lid -> (FStar_List.append lid.ns ((lid.ident)::[])))

let lid_of_ids = (fun ids -> (let _22_26 = (FStar_Util.prefix ids)
in (match (_22_26) with
| (ns, id) -> begin
(let nsstr = (let _113_46 = (FStar_List.map text_of_id ns)
in (FStar_All.pipe_right _113_46 text_of_path))
in {ns = ns; ident = id; nsstr = nsstr; str = if (nsstr = "") then begin
id.idText
end else begin
(Prims.strcat (Prims.strcat nsstr ".") id.idText)
end})
end)))

let lid_of_path = (fun path pos -> (let ids = (FStar_List.map (fun s -> (mk_ident (s, pos))) path)
in (lid_of_ids ids)))

let text_of_lid = (fun lid -> lid.str)

let lid_equals = (fun l1 l2 -> (l1.str = l2.str))

let lid_with_range = (fun lid r -> (let id = (let _22_37 = lid.ident
in {idText = _22_37.idText; idRange = r})
in (let _22_40 = lid
in {ns = _22_40.ns; ident = id; nsstr = _22_40.nsstr; str = _22_40.str})))

let range_of_lid = (fun lid -> lid.ident.idRange)

let set_lid_range = (fun l r -> (let ids = (FStar_All.pipe_right (FStar_List.append l.ns ((l.ident)::[])) (FStar_List.map (fun i -> (mk_ident (i.idText, r)))))
in (lid_of_ids ids)))




