(*
   Copyright 2008-2018 Microsoft Research

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
#light "off"
module FStar.Interactive.CompletionTable

open FStar
open FStar.All

let string_compare s1 s2 =
  String.compare s1 s2

(** * (Pairing) min-heaps * **)

type heap<'a> =
| EmptyHeap
| Heap of 'a * list<heap<'a>>

let heap_merge cmp h1 h2 =
  match h1, h2 with
  | EmptyHeap, h
  | h, EmptyHeap -> h
  | Heap (v1, hh1), Heap (v2, hh2) ->
    if cmp v1 v2 < 0 then Heap (v1, h2 :: hh1) else Heap (v2, h1 :: hh2)

let heap_insert cmp h v =
  heap_merge cmp (Heap (v, [])) h

let rec heap_merge_pairs cmp = function
  | [] -> EmptyHeap
  | [h] -> h
  | h1 :: h2 :: hh ->
    heap_merge cmp (heap_merge cmp h1 h2) (heap_merge_pairs cmp hh)

let heap_peek = function
  | EmptyHeap -> None
  | Heap (v, _) -> Some v

let heap_pop cmp = function
  | EmptyHeap -> None
  | Heap (v, hh) -> Some (v, heap_merge_pairs cmp hh)

let heap_from_list cmp values =
  List.fold_left (heap_insert cmp) EmptyHeap values

(** * List functions * **)

let push_nodup key_fn x = function
  | [] -> [x]
  | h :: t -> if string_compare (key_fn x) (key_fn h) = 0 then h :: t else x :: h :: t

let rec add_priorities n acc = function
  | [] -> acc
  | h :: t -> add_priorities (n + 1) ((n, h) :: acc) t

(** Merge ‘lists’, a list of increasing (according to ‘key_fn’) lists.
    Keeps a single copy of each key that appears in more than one list (earlier
    lists take precedence when chosing which value to keep). *)
let merge_increasing_lists_rev (key_fn: 'a -> string) (lists: list<list<'a>>) =
  let cmp v1 v2 =
    match v1, v2 with
    | (_, []), _ | _, (_, []) -> failwith "impossible"
    | (pr1, h1 :: _), (pr2, h2 :: _) ->
      let cmp_h = string_compare (key_fn h1) (key_fn h2) in
      if cmp_h <> 0 then cmp_h else pr1 - pr2 in
  let rec aux (lists: heap<(int * list<'a>)>) (acc: list<'a>) =
    match heap_pop cmp lists with
    | None -> acc
    | Some ((pr, []), _) -> failwith "impossible"
    | Some ((pr, [v]), lists) -> aux lists (push_nodup key_fn v acc)
    | Some ((pr, v :: tl), lists) -> aux (heap_insert cmp lists (pr, tl)) (push_nodup key_fn v acc) in
  let lists = List.filter (fun x -> x <> []) lists in
  match lists with
  | [] -> [] | [l] -> List.rev l
  | _ ->
    let lists = add_priorities 0 [] lists in
    aux (heap_from_list cmp lists) []

(** * Binary trees * **)

type btree<'a> =
| StrEmpty
| StrBranch of string * 'a * (btree<'a>) * (btree<'a>)
(* (key: string) * (value: 'a) * (lbt: btree 'a) * (rbt: btree 'a) *)

let rec btree_to_list_rev btree acc =
  match btree with
  | StrEmpty -> acc
  | StrBranch (key, value, lbt, rbt) ->
    btree_to_list_rev rbt ((key, value) :: btree_to_list_rev lbt acc)

let rec btree_from_list nodes size =
  if size = 0 then (StrEmpty, nodes)
  else
    let lbt_size = size / 2 in
    let rbt_size = size - lbt_size - 1 in
    let lbt, nodes_left = btree_from_list nodes lbt_size in
    match nodes_left with
    | [] -> failwith "Invalid size passed to btree_from_list"
    | (k, v) :: nodes_left ->
      let rbt, nodes_left = btree_from_list nodes_left rbt_size in
      StrBranch (k, v, lbt, rbt), nodes_left

let rec btree_insert_replace (bt: btree<'a>) (k: string) (v: 'a) : btree<'a> =
  match bt with
  | StrEmpty -> StrBranch (k, v, StrEmpty, StrEmpty)
  | StrBranch (k', v', lbt, rbt) ->
    let cmp = string_compare k k' in
    if cmp < 0 then
      StrBranch (k', v', btree_insert_replace lbt k v, rbt)
    else if cmp > 0 then
      StrBranch (k', v', lbt, btree_insert_replace rbt k v)
    else
      StrBranch (k', v, lbt, rbt)

let rec btree_find_exact (bt: btree<'a>) (k: string) : option<'a> =
  match bt with
  | StrEmpty -> None
  | StrBranch (k', v, lbt, rbt) ->
    let cmp = string_compare k k' in
    if cmp < 0 then
      btree_find_exact lbt k
    else if cmp > 0 then
      btree_find_exact rbt k
    else
      Some v

let rec btree_extract_min (bt: btree<'a>) : option<(string * 'a * btree<'a>)> =
  match bt with
  | StrEmpty -> None
  | StrBranch (k, v, StrEmpty, rbt) -> Some (k, v, rbt)
  | StrBranch (_, _, lbt, _) -> btree_extract_min lbt

let rec btree_remove (bt: btree<'a>) (k: string) : btree<'a> =
  match bt with
  | StrEmpty -> StrEmpty
  | StrBranch (k', v, lbt, rbt) ->
    let cmp = string_compare k k' in
    if cmp < 0 then
      StrBranch (k', v, btree_remove lbt k, rbt)
    else if cmp > 0 then
      StrBranch (k', v, lbt, btree_remove rbt k)
    else
      match lbt with
      | StrEmpty -> bt
      | _ -> match btree_extract_min rbt with
            | None -> lbt
            | Some (rbt_min_k, rbt_min_v, rbt') ->
              StrBranch (rbt_min_k, rbt_min_v, lbt, rbt')

type prefix_match =
  { prefix: option<string>;
    completion: string }

type path_elem =
  { imports: list<string>;
    segment: prefix_match }

let matched_prefix_of_path_elem (elem: path_elem) = elem.segment.prefix

let mk_path_el imports segment = { imports = imports; segment = segment }

let rec btree_find_prefix (bt: btree<'a>) (prefix: string)
    : list<(prefix_match * 'a)> (* ↑ keys *) =
  let rec aux (bt: btree<'a>) (prefix: string) (acc: list<(prefix_match * 'a)>) : list<(prefix_match * 'a)> =
    match bt with
    | StrEmpty -> acc
    | StrBranch (k, v, lbt, rbt) ->
      let cmp = string_compare k prefix in
      let include_middle = Util.starts_with k prefix in
      let explore_right = cmp <= 0 || include_middle in
      let explore_left = cmp > 0 in
      let matches =
        if explore_right then aux rbt prefix acc else acc in
      let matches =
        if include_middle then
          ({ prefix = Some prefix; completion = k }, v) :: matches
        else
          matches in
      let matches =
        if explore_left then aux lbt prefix matches else matches in
      matches in
  aux bt prefix []

let rec btree_fold (bt: btree<'a>) (f: string -> 'a -> 'b -> 'b) (acc: 'b) =
  match bt with
  | StrEmpty -> acc
  | StrBranch (k, v, lbt, rbt) ->
    btree_fold lbt f (f k v (btree_fold rbt f acc))

(** * Tries * **)

type path = list<path_elem>
type query = list<string>

let query_to_string q = String.concat "." q

type name_collection<'a> =
| Names of btree<'a>
| ImportedNames of string * names<'a>
and names<'a> = list<name_collection<'a>>

type trie<'a> =
  { bindings: names<'a>;
    namespaces: names<trie<'a>> }

let trie_empty = { bindings = []; namespaces = [] }

let rec names_find_exact (names: names<'a>) (ns: string) : option<'a> =
  let result, names =
    match names with
    | [] -> None, None
    | Names bt :: names ->
      btree_find_exact bt ns, Some names
    | ImportedNames (_, names) :: more_names ->
      names_find_exact names ns, Some more_names in
  match result, names with
  | None, Some scopes -> names_find_exact scopes ns
  | _ -> result

let rec trie_descend_exact (tr: trie<'a>) (query: query) : option<trie<'a>> =
  match query with
  | [] -> Some tr
  | ns :: query ->
    Util.bind_opt (names_find_exact tr.namespaces ns)
      (fun scope -> trie_descend_exact scope query)

let rec trie_find_exact (tr: trie<'a>) (query: query) : option<'a> =
  match query with
  | [] -> failwith "Empty query in trie_find_exact"
  | [name] -> names_find_exact tr.bindings name
  | ns :: query ->
    Util.bind_opt (names_find_exact tr.namespaces ns)
      (fun scope -> trie_find_exact scope query)

let names_insert (name_collections: names<'a>) (id: string) (v: 'a) : names<'a> =
  let bt, name_collections =
    match name_collections with
    | Names bt :: tl -> (bt, tl)
    | _ -> (StrEmpty, name_collections) in
  Names (btree_insert_replace bt id v) :: name_collections

let rec namespaces_mutate (namespaces: names<trie<'a>>) (ns: string) (q: query)
                          (rev_acc: query)
                          (mut_node: trie<'a> -> string -> query -> query -> names<trie<'a>> -> trie<'a>)
                          (mut_leaf: trie<'a> -> query -> trie<'a>)=
  let trie = Util.dflt trie_empty (names_find_exact namespaces ns) in
  names_insert namespaces ns (trie_mutate trie q rev_acc mut_node mut_leaf)

and trie_mutate (tr: trie<'a>) (q: query) (rev_acc: query)
                (mut_node: trie<'a> -> string -> query -> query -> names<trie<'a>> -> trie<'a>)
                (mut_leaf: trie<'a> -> query -> trie<'a>) : trie<'a> =
  match q with
  | [] ->
    mut_leaf tr rev_acc
  | id :: q ->
    let ns' = namespaces_mutate tr.namespaces id q (id :: rev_acc) mut_node mut_leaf in
    mut_node tr id q rev_acc ns'

let trie_mutate_leaf (tr: trie<'a>) (query: query) =
  trie_mutate tr query [] (fun tr _ _ _ namespaces -> { tr with namespaces = namespaces })

let trie_insert (tr: trie<'a>) (ns_query: query) (id: string) (v: 'a) : trie<'a> =
  trie_mutate_leaf tr ns_query (fun tr _ -> { tr with bindings = names_insert tr.bindings id v })

let trie_import (tr: trie<'a>) (host_query: query) (included_query: query)
                (mutator: trie<'a> -> trie<'a> -> string -> trie<'a>) =
  let label = query_to_string included_query in
  let included_trie = Util.dflt trie_empty (trie_descend_exact tr included_query) in
  trie_mutate_leaf tr host_query (fun tr _ -> mutator tr included_trie label)

let trie_include (tr: trie<'a>) (host_query: query) (included_query: query)
    : trie<'a> =
  trie_import tr host_query included_query (fun tr inc label ->
      { tr with bindings = ImportedNames (label, inc.bindings) :: tr.bindings })

let trie_open_namespace (tr: trie<'a>) (host_query: query) (included_query: query)
    : trie<'a> =
  trie_import tr host_query included_query (fun tr inc label ->
      { tr with namespaces = ImportedNames (label, inc.namespaces) :: tr.namespaces })

let trie_add_alias (tr: trie<'a>) (key: string)
                   (host_query: query) (included_query: query) : trie<'a> =
  trie_import tr host_query included_query (fun tr inc label ->
      // Very similar to an include, but aliasing A.B as M in A.C entirely
      // overrides A.B.M, should that also exists.  Doing this makes sense
      // because we only process aliases in the current module.
      trie_mutate_leaf tr [key] (fun _ignored_overwritten_trie _ ->
          { bindings = [ImportedNames (label, inc.bindings)]; namespaces = [] }))

let names_revmap (fn: btree<'a> -> 'b) (name_collections: names<'a> (* ↓ priority *))
    : list<(list<string> (* imports *) * 'b)> (* ↑ priority *) =
  let rec aux (acc: list<(list<string> * 'b)>)
              (imports: list<string>) (name_collections: names<'a>)
      : list<(list<string> * 'b)> (* #1158 *) =
    List.fold_left (fun acc -> function
        | Names bt -> (imports, fn bt) :: acc
        | ImportedNames (nm, name_collections) ->
          aux acc (nm :: imports) name_collections)
      acc name_collections in
  aux [] [] name_collections

let btree_find_all (prefix: option<string>) (bt: btree<'a>)
    : list<(prefix_match * 'a)> (* ↑ keys *) =
  btree_fold bt (fun k tr acc ->
      ({ prefix = prefix; completion = k }, tr) :: acc) []

type name_search_term =
| NSTAll
| NSTNone
| NSTPrefix of string

let names_find_rev (names: names<'a>) (id: name_search_term) : list<(path_elem * 'a)> =
  let matching_values_per_collection_with_imports =
    match id with
    | NSTNone -> []
    | NSTAll -> names_revmap (btree_find_all None) names
    | NSTPrefix "" -> names_revmap (btree_find_all (Some "")) names
    | NSTPrefix id -> names_revmap (fun bt -> btree_find_prefix bt id) names in
  let matching_values_per_collection =
    List.map (fun (imports, matches) ->
                List.map (fun (segment, v) -> mk_path_el imports segment, v) matches)
             matching_values_per_collection_with_imports in
  merge_increasing_lists_rev
    (fun (path_el, _) -> path_el.segment.completion) matching_values_per_collection

let rec trie_find_prefix' (tr: trie<'a>) (path_acc: path)
                          (query: query) (acc: list<(path * 'a)>)
    : list<(path * 'a)> =
  let ns_search_term, bindings_search_term, query =
    match query with
    | [] -> NSTAll, NSTAll, []
    | [id] -> NSTPrefix id, NSTPrefix id, []
    | ns :: query -> NSTPrefix ns, NSTNone, query in

  let matching_namespaces_rev = names_find_rev tr.namespaces ns_search_term in
  let acc_with_recursive_bindings =
    List.fold_left (fun acc (path_el, trie) ->
        trie_find_prefix' trie (path_el :: path_acc) query acc)
      acc matching_namespaces_rev in

  let matching_bindings_rev = names_find_rev tr.bindings bindings_search_term in
  List.rev_map_onto (fun (path_el, v) -> (List.rev (path_el :: path_acc), v))
    matching_bindings_rev acc_with_recursive_bindings

let trie_find_prefix (tr: trie<'a>) (query: query) : list<(path * 'a)> =
  trie_find_prefix' tr [] query []

(** * High level interface * **)

type ns_info = { ns_name: string;
                 ns_loaded: bool }

type mod_info = { mod_name: string;
                  mod_path: string;
                  mod_loaded: bool }

let mod_name md = md.mod_name

type mod_symbol =
| Module of mod_info
| Namespace of ns_info

type lid_symbol = Ident.lid

type symbol =
| ModOrNs of mod_symbol
| Lid of lid_symbol

type table =
  { tbl_lids: trie<lid_symbol>;
    tbl_mods: trie<mod_symbol> }

let empty : table =
  { tbl_lids = trie_empty;
    tbl_mods = trie_empty }

// Note that we never add aliases to tbl_mods: we use tbl_mods only for
// completion of opens and includes, and these take full module paths.
// Inclusions handling would have to be reinstated should we wish to also
// complete partial names of unloaded (e.g. [open FStar // let x = List._] when
// FStar.List isn't loaded).

let insert (tbl: table) (host_query: query) (id: string) (c: lid_symbol) : table =
  { tbl with tbl_lids = trie_insert tbl.tbl_lids host_query id c }

let register_alias (tbl: table) (key: string) (host_query: query) (included_query: query) : table =
  { tbl with tbl_lids = trie_add_alias tbl.tbl_lids key host_query included_query }

let register_include (tbl: table) (host_query: query) (included_query: query) : table =
  { tbl with tbl_lids = trie_include tbl.tbl_lids host_query included_query }

let register_open (tbl: table) (is_module: bool) (host_query: query) (included_query: query) : table =
  if is_module then
    // We only process module opens for the current module, where they are just like includes
    register_include tbl host_query included_query
  else
    { tbl with tbl_lids = trie_open_namespace tbl.tbl_lids host_query included_query }

let register_module_path (tbl: table) (loaded: bool) (path: string) (mod_query: query) =
  let ins_ns id bindings full_name loaded =
    match names_find_exact bindings id, loaded with
    | None, _ // Never seen before
    | Some (Namespace { ns_loaded = false }), true -> // Seen, but not loaded yet
      names_insert bindings id
        (Namespace ({ ns_name = full_name; ns_loaded = loaded }))
    | Some _, _ -> // Already seen as a loaded namespace, or as a module
      bindings in
  let ins_mod id bindings full_name loaded =
    names_insert bindings id
      (Module ({ mod_name = full_name; mod_loaded = loaded; mod_path = path })) in
  let name_of_revq query =
    String.concat "." (List.rev query) in
  let ins id q revq bindings loaded =
    let name = name_of_revq (id :: revq) in
    match q with
    | [] -> ins_mod id bindings name loaded
    | _ -> ins_ns id bindings name loaded in
  { tbl with tbl_mods =
    trie_mutate tbl.tbl_mods mod_query [] (fun tr id q revq namespaces ->
        { tr with namespaces = namespaces;
                  bindings = ins id q revq tr.bindings loaded })
      (fun tr _ -> tr) }

let string_of_path (path: path) : string =
  String.concat "." (List.map (fun el -> el.segment.completion) path)

let match_length_of_path (path: path) : int =
  let length, (last_prefix, last_completion_length) =
    List.fold_left
      (fun acc elem ->
         let (acc_len, _) = acc in
         match elem.segment.prefix with
         | Some prefix ->
           let completion_len = String.length elem.segment.completion in
           (acc_len + 1 (* ‘.’ *) + completion_len, (prefix, completion_len))
         | None -> acc)
      (0, ("", 0)) path in
  length
  - 1 (* extra ‘.’ *)
  - last_completion_length
  + (String.length last_prefix) (* match stops after last prefix *)

let first_import_of_path (path: path) : option<string> =
  match path with
  | [] -> None
  | { imports = imports } :: _ -> List.last imports

let alist_of_ns_info ns_info =
  [("name", FStar.Util.JsonStr ns_info.ns_name);
   ("loaded", FStar.Util.JsonBool ns_info.ns_loaded)]

let alist_of_mod_info mod_info =
  [("name", FStar.Util.JsonStr mod_info.mod_name);
   ("path", FStar.Util.JsonStr mod_info.mod_path);
   ("loaded", FStar.Util.JsonBool mod_info.mod_loaded)]

type completion_result =
  { completion_match_length: int;
    completion_candidate: string;
    completion_annotation: string }

let json_of_completion_result (result: completion_result) =
  Util.JsonList [Util.JsonInt result.completion_match_length;
                 Util.JsonStr result.completion_annotation;
                 Util.JsonStr result.completion_candidate]

let completion_result_of_lid (path, _lid) =
  { completion_match_length = match_length_of_path path;
    completion_candidate = string_of_path path;
    completion_annotation = Util.dflt "" (first_import_of_path path) }

let completion_result_of_mod annot loaded path =
  { completion_match_length = match_length_of_path path;
    completion_candidate = string_of_path path;
    completion_annotation = Util.format1 (if loaded then " %s " else "(%s)") annot }

let completion_result_of_ns_or_mod (path, symb) =
  match symb with
  | Module { mod_loaded = loaded } -> completion_result_of_mod "mod" loaded path
  | Namespace { ns_loaded = loaded } -> completion_result_of_mod "ns" loaded path

let find_module_or_ns (tbl:table) (query:query) =
  trie_find_exact tbl.tbl_mods query

let autocomplete_lid (tbl: table) (query: query) =
  List.map completion_result_of_lid (trie_find_prefix tbl.tbl_lids query)

let autocomplete_mod_or_ns (tbl: table) (query: query) (filter: (path * mod_symbol) -> option<(path * mod_symbol)>) =
  trie_find_prefix tbl.tbl_mods query
  |> List.filter_map filter
  |> List.map completion_result_of_ns_or_mod
