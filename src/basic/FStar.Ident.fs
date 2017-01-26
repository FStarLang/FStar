#light "off"
module FStar.Ident
open FStar.Range

type ident = {idText:string;
              idRange:Range.range}

type lident = {ns:list<ident>; //["FStar"; "Basic"]
               ident:ident;    //"lident"
               nsstr:string; // Cached version of the namespace
               str:string} // Cached version of string_of_lid

type lid = lident

let mk_ident (text,range) = {idText=text; idRange=range}
let reserved_prefix = "uu___"
let gen =
    let x = Util.mk_ref 0 in
    fun r -> x := !x + 1; mk_ident (reserved_prefix ^ string_of_int !x, r)
let id_of_text str = mk_ident(str, dummyRange)
let text_of_id (id:ident) = id.idText
let text_of_path path = Util.concat_l "." path
let path_of_text text = String.split ['.'] text
let path_of_ns ns = List.map text_of_id ns
let path_of_lid lid = List.map text_of_id (lid.ns@[lid.ident])
let ids_of_lid lid = lid.ns@[lid.ident]
let lid_of_ids ids =
    let ns, id = Util.prefix ids in
    let nsstr = List.map text_of_id ns |> text_of_path in
    {ns=ns;
     ident=id;
     nsstr=nsstr;
     str=(if nsstr="" then id.idText else nsstr ^ "." ^ id.idText)}
let lid_of_path path pos =
    let ids = List.map (fun s -> mk_ident(s, pos)) path in
    lid_of_ids ids
let text_of_lid lid = lid.str
let lid_equals l1 l2 = l1.str = l2.str
let ident_equals id1 id2 = id1.idText = id2.idText
let range_of_lid (lid:lid) = lid.ident.idRange
let set_lid_range l r = {l with ident={l.ident with idRange=r}}
let lid_add_suffix l s =
    let path = path_of_lid l in
    lid_of_path (path@[s]) (range_of_lid l)

(* JP: I don't understand why a lid has both a str and a semantic list of
 * namespaces followed by a lowercase identifiers... *)
let string_of_lid lid = text_of_path (path_of_lid lid)
