module FStar.Ident

open Prims
open FStar.Compiler.Effect
open FStar.Compiler.Range
open FStar.Compiler.List
module List = FStar.Compiler.List
module Util = FStar.Compiler.Util

type ident_t 'a = { idText : 'a ; idRange : range }
let ident_t_to_yojson (f:'a -> 'b) (x:ident_t 'a) = f x.idText
let ident_t_of_yojson (f:'a -> 'b) (x:'a) = failwith "Parsing from JSON is not yet supported"
let pp_ident_t (f:'a -> 'b -> 'c) (fmt:'a) (x:ident_t 'b) = f fmt x.idText

[@@ PpxDerivingYoJson; PpxDerivingShow ]
type ident = ident_t string

type lident_t 'a = {ns:ipath; //["FStar"; "Basic"]
                   ident:ident;    //"lident"
                   nsstr:string; // Cached version of the namespace
                   str:'a} // Cached version of string_of_lid

let lident_t_to_yojson (f:'a -> 'b) (x:lident_t 'a) = f x.str
let lident_t_of_yojson (f:'a -> 'b) (x:'a) = failwith "Parsing from JSON is not yet supported"
let pp_lident_t (f:'a -> 'b -> 'c) (fmt:'a) (x:lident_t 'b) = f fmt x.str

[@@ PpxDerivingYoJson; PpxDerivingShow ]
type lident = lident_t string

let mk_ident (text,range) = {idText=text; idRange=range}

let set_id_range r i = { i with idRange=r }

let reserved_prefix = "uu___"
let _gen, _secret_ref =
    let x = Util.mk_ref 0 in
    let next_id () = let v = !x in x := v + 1; v in
    let reset () = x := 0 in
    (next_id, reset), x

let next_id () = fst _gen ()
let reset_gensym () = snd _gen ()

let with_frozen_gensym f =
  let v = !_secret_ref in
  let r =
    try f () with
    | e -> (_secret_ref := v; raise e)
  in
  _secret_ref := v;
  r

let gen' s r =
    let i = next_id() in
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
