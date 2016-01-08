module FStar.Ident
open FStar.Range

type ident = {idText:string;
              idRange:Range.range}

type lident = {ns:list<ident>; //["Microsoft"; "FStar"; "Absyn"; "Syntax"]
               ident:ident;    //"LongIdent"
               nsstr:string;
               str:string}

type lid = lident

let mk_ident (text,range) = {idText=text; idRange=range}
let gen = 
    let x = ref 0 in 
    fun r -> incr x; mk_ident ("@x_" ^ string_of_int !x, r)
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
let lid_with_range (lid:lid) (r:Range.range) =
    let id = {lid.ident with idRange=r} in
    {lid with ident=id}
let range_of_lid (lid:lid) = lid.ident.idRange
let set_lid_range l r =
  let ids = (l.ns@[l.ident]) |> List.map (fun i -> mk_ident(i.idText, r)) in
  lid_of_ids ids
