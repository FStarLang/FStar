module FStarC.Ident

open Prims
open FStarC.Effect
open FStarC.Range
open FStarC.List
module List = FStarC.List
module Util = FStarC.Util
module GS = FStarC.GenSym

[@@ PpxDerivingYoJson; PpxDerivingShow ]
type ident = {idText:string;
              idRange:range}

[@@ PpxDerivingYoJson; PpxDerivingShow ]
type lident = {ns:ipath; //["FStar"; "Basic"]
               ident:ident;    //"lident"
               nsstr:string; // Cached version of the namespace
               str:string} // Cached version of string_of_lid

let mk_ident (text,range) = {idText=text; idRange=range}

let set_id_range r i = { i with idRange=r }

let reserved_prefix = "uu___"

let gen' s r =
    let i = GS.next_id() in
    mk_ident (s ^ string_of_int i, r)

let gen r = gen' reserved_prefix r

let ident_of_lid l = l.ident

let range_of_id (id:ident) = id.idRange
let id_of_text str = mk_ident(str, dummyRange)
let string_of_id (id:ident) = id.idText
let text_of_path path = Util.concat_l "." path
let path_of_text text = String.split ['.'] text
let path_of_ns ns = List.map string_of_id ns
let path_of_lid lid = List.map string_of_id (lid.ns@[lid.ident])
let ns_of_lid lid = lid.ns
let ids_of_lid lid = lid.ns@[lid.ident]
let lid_of_ns_and_id ns id =
    let nsstr = List.map string_of_id ns |> text_of_path in
    {ns=ns;
     ident=id;
     nsstr=nsstr;
     str=(if nsstr="" then id.idText else nsstr ^ "." ^ id.idText)}
let lid_of_ids ids =
    let ns, id = Util.prefix ids in
    lid_of_ns_and_id ns id
let lid_of_str str =
    lid_of_ids (List.map id_of_text (Util.split str "."))
let lid_of_path path pos =
    let ids = List.map (fun s -> mk_ident(s, pos)) path in
    lid_of_ids ids
let text_of_lid lid = lid.str
let lid_equals l1 l2 = l1.str = l2.str
let ident_equals id1 id2 = id1.idText = id2.idText
let range_of_lid (lid:lid) = range_of_id lid.ident
let set_lid_range l r = {l with ident={l.ident with idRange=r}}
let lid_add_suffix l s =
    let path = path_of_lid l in
    lid_of_path (path@[s]) (range_of_lid l)

let ml_path_of_lid lid =
    String.concat "_" <| (path_of_ns lid.ns)@[string_of_id lid.ident]

let string_of_lid lid = lid.str

let qual_id lid id =
    set_lid_range (lid_of_ids (lid.ns @ [lid.ident;id])) (range_of_id id)

let nsstr (l:lid) : string = l.nsstr

instance showable_ident = {
  show = string_of_id;
}
instance showable_lident = {
  show = string_of_lid;
}
let pretty_ident = pretty_from_showable
let pretty_lident = pretty_from_showable
instance hasrange_ident = {
  pos = range_of_id;
  setPos = (fun rng id -> { id with idRange = rng });
}
instance hasrange_lident = {
  pos = (fun lid -> Class.HasRange.pos lid.ident);
  setPos = (fun rng id -> { id with ident = setPos rng id.ident });
}
instance deq_ident = {
  (=?) = ident_equals;
}
instance deq_lident = {
  (=?) = lid_equals;
}

instance ord_ident = {
  super = deq_ident;
  cmp = (fun x y -> cmp (string_of_id x) (string_of_id y));
}

instance ord_lident = {
  super = deq_lident;
  cmp = (fun x y -> cmp (string_of_lid x) (string_of_lid y));
}
