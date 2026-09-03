(*
   Copyright 2008-2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStarC.Custard.Unit

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Class.Show
open FStarC.Custard.Syntax
open FStarC.Errors
open FStarC.Pprint

module BU  = FStarC.Format
module U   = FStarC.Util
module E   = FStarC.Errors
module O   = FStarC.Options
module SMap = FStarC.SMap

let current_version = 11

(* The IR is plain first-order data -- no references, no closures, no
   hashconsing -- so the same mechanism that stores checked files stores a
   `.cui` as well.  A hand-written printer and parser would be several hundred
   lines that have to be kept in step with an IR still very much in flux, and
   they would buy nothing a version check does not: a `.cui` is a build
   artifact, not something a user edits.  --custard_dump_cui covers the case
   where a human wants to look. *)

let layout_options () : ML (list (string & string)) =
  (* Only the options that can change what an interface *means*.  Printing and
     debugging options are deliberately absent: two units built with different
     --custard_dump_ir settings still agree about layout, and refusing to link
     them would be gratuitous. *)
  [ "custard_backend",            O.custard_backend ();
    "custard_monomorphize_types", string_of_bool (O.custard_monomorphize_types ()) ]

let write_iface (fn:string) (i:iface) : ML unit =
  U.save_value_to_file fn i

let bad (#a:Type) (fn:string) (msg:list document) : ML a =
  E.raise_error0 E.Error_CustardBadUnitInterface
    (text (BU.fmt1 "Cannot link the Custard unit interface %s." fn) :: msg)

let read_iface (fn:string) : ML iface =
  let i : iface =
    match U.load_value_from_file fn with
    | Some i -> i
    | None ->
      bad fn [text "The file is missing or could not be read."]
  in
  let h = i.ui_header in
  if h.uh_version <> current_version then
    bad fn [
      text (BU.fmt2 "It was written by a different version of Custard \
                        (format %s, but this F* speaks %s)."
              (show h.uh_version) (show current_version));
      text "Rebuild the unit."
    ];
  let mine = layout_options () in
  (* An option mismatch is a miscompilation waiting to happen, not a warning:
     a unit built with --custard_monomorphize_types lays its types out
     differently from one built without, and the interface has no way to say
     so beyond this check. *)
  mine |> List.iter (fun (k, v) ->
    match List.tryFind (fun (k', _) -> k = k') h.uh_options with
    | Some (_, v') when v = v' -> ()
    | Some (_, v') ->
      bad fn [
        text (BU.fmt3 "It was built with --%s %s, but this run uses %s."
                k v' v);
        text "Layout decisions depend on that option, so the two cannot be mixed."
      ]
    | None ->
      bad fn [text (BU.fmt1 "It records no value for --%s." k)]);
  i

(** {1 Dumping} *)

let type_info_to_string (ti:type_info) : ML string =
  let l =
    match ti.ti_layout with
    | L_erased     -> "erased"
    | L_newtype nt -> BU.fmt1 "newtype(%s)" nt.nt_field
    | L_struct cls -> BU.fmt1 "struct(%s ctors)" (show (List.length cls))
    | L_abbrev _   -> "abbrev"
    | L_opaque     -> "opaque"
  in
  if ti.ti_erased then l ^ ", erased" else l

let entry_to_string (e:entry) : ML string =
  let what =
    match e.ue_decl with
    | DType d ->
      BU.fmt2 "type %s [%s]" (show d.dt_name)
        (match e.ue_type with
         | Some ti -> type_info_to_string ti
         | None    -> "?")
    | DLet d      -> BU.fmt1 "let %s"      (show d.dl_name)
    | DExternal d -> BU.fmt1 "external %s" (show d.dx_name)
    | DExn d      -> BU.fmt1 "exception %s" (show d.de_name)
  in
  BU.fmt3 "  %s\n    key: %s%s\n" what e.ue_key
    (match e.ue_home with Some m -> "\n    home: " ^ m | None -> "")

let iface_to_string (i:iface) : ML string =
  let h = i.ui_header in
  let opt (label:string) (v:option string) : string =
    match v with Some f -> "\n  " ^ label ^ ": " ^ f | None -> "" in
  BU.fmt4 "unit %s (format %s, backend %s)%s"
    h.uh_name (show h.uh_version) h.uh_backend
    (opt "header" h.uh_header ^ opt "init" h.uh_init ^ "\n" ^
     BU.fmt3 "  options: %s\n  %s checked files\n\n%s"
       (String.concat ", " (h.uh_options |> List.map (fun (k, v) -> k ^ "=" ^ v)))
       (show (List.length h.uh_digests))
       (String.concat "" (i.ui_entries |> List.map entry_to_string)))

(** {1 The index} *)

(* What a linked unit is, beyond the entries it contributed.  Kept in
   [--custard_link] order because section 42.3's [main] calls the
   initializers in that order, and a hash table has no order to offer. *)
type unit_ref = {
  ur_name:   string;
  ur_header: option string;
  ur_init:   option string;
}

(* [string & entry]: the unit an entry came from, kept alongside it so a
   backend can qualify the name without a second lookup. *)
type links = {
  lk_tbl:   SMap.t (string & entry);
  lk_units: list unit_ref;   (* in --custard_link order *)
}

let empty_links : links = { lk_tbl = SMap.create 1; lk_units = [] }

let load_links (fns:list string) : ML links =
  let tbl : SMap.t (string & entry) = SMap.create 1000 in
  (* [List.map] rather than a reference, so that [lk_units] comes out in
     --custard_link order without a reversal to get wrong. *)
  let units = fns |> List.map (fun fn ->
    let i = read_iface fn in
    let u = i.ui_header.uh_name in
    i.ui_entries |> List.iter (fun e ->
      match SMap.try_find tbl e.ue_key with
      | Some (u', _) when u' <> u ->
        (* Which unit a request resolves to would otherwise depend on the
           order of the --custard_link flags, and the two copies may well have
           different layouts.  Section 12.6 allows a specialization to be
           duplicated across *sibling* units; it does not allow both of them to
           be linked into the same program. *)
        bad fn [
          text (BU.fmt2 "Both %s and %s export a definition for the same \
                            specialization key." u' u);
          text (BU.fmt1 "The key is: %s" e.ue_key);
          text "Link only one of them, or merge the two units."
        ]
      | _ -> SMap.add tbl e.ue_key (u, e));
    { ur_name   = u;
      ur_header = i.ui_header.uh_header;
      ur_init   = i.ui_header.uh_init }) in
  if O.custard_dump_cui () && fns <> [] then
    BU.print1 "Custard: linked %s specializations.\n" (show (List.length (SMap.keys tbl)));
  { lk_tbl = tbl; lk_units = units }

let lookup (l:links) (k:string) : ML (option (string & entry)) =
  SMap.try_find l.lk_tbl k

let is_empty (l:links) : ML bool = SMap.keys l.lk_tbl = [] && Nil? l.lk_units

let link_homes (l:links) : ML (list string) =
  SMap.fold l.lk_tbl (fun _ (_, e) acc ->
    match e.ue_home with
    | Some h -> if List.mem h acc then acc else h :: acc
    | None -> acc) []

(* A unit contributing no entry still contributes a header and an
   initializer: it may have exported nothing this run happened to request and
   still have globals that have to be set up. *)
let link_headers (l:links) : ML (list string) =
  l.lk_units |> List.collect (fun u ->
    match u.ur_header with Some h -> [h] | None -> [])

let link_inits (l:links) : ML (list string) =
  l.lk_units |> List.collect (fun u ->
    match u.ur_init with Some i -> [i] | None -> [])
