// -*- fstar-subp-prover-args: ("--eager_inference" "--lax" "--MLish" "--include" "../../ulib" "--include" "../u_boot_fsts" "--include" "../boot_fstis") -*-

#light "off"
module FStar.Interactive.CompletionTable

open FStar
open FStar.All
module BU = FStar.Util

module String = begin
  let compare = compare
  let uppercase (s: string) = s.ToUpperInvariant ()
end

module List = begin
  let filter_map f l =
      (let rec filter_map acc l =
         match l with
         | [] ->
             List.rev acc
         | hd :: tl ->
             match f hd with
             | Some hd ->
                 filter_map (hd :: acc) tl
             | None ->
                 filter_map acc tl
       in
       filter_map [] l)

  let rev_map_onto f l acc = List.fold (fun acc x -> f x :: acc) acc l

  let fold_left = List.fold

  let hd = List.head

  let rec rev_acc = (fun ( l  :  'a list ) ( acc  :  'a list ) ->
                     (match (l) with
                      | [] -> begin
                                 acc
                             end
                      | hd::tl -> begin
                                    (rev_acc tl ((hd)::acc))
                                end))

  let rev_append l a = rev_acc l a
end
module All = begin end
module BU = begin
    let bind_opt opt f =
        match opt with
        | None -> None
        | Some x -> f x
    let dflt x = function
        | None   -> x
        | Some x -> x
    let format1 msg arg = msg ^ arg
    let starts_with = fun (s: string) pref -> s.StartsWith pref
end

let string_compare s1 s2 =
  String.compare s1 s2 // (String.uppercase s1) (String.uppercase s2)

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
    | Some ((pr, v :: []), lists) -> aux lists (v :: acc)
    | Some ((pr, v :: tl), lists) -> aux (heap_insert cmp lists (pr, tl)) (push_nodup key_fn v acc) in
  let lists = List.filter (fun x -> x <> []) lists in
  match lists with
  | [] -> [] | [l] -> l
  | _ ->
    let lists = add_priorities 0 [] lists in
    aux (heap_from_list cmp lists) []

let test_merge () =
  let l1 = List.rev [("And", 7); ("admitP", 5); ("2", 2); ("1", 1)] in
  let l2 = List.rev [("And", 77); ("admitP", 66); ("5", 55); ("3", 3); ("1", 1)] in
  let l3 = List.rev [("And", 777); ("admitP", 555); ("4", 4); ("1", 1)] in
  merge_increasing_lists_rev (fun (k, _) -> k) [l1;l2;l3]

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

type path_elem = option<string>*string

let rec btree_find_prefix (bt: btree<'a>) (prefix: string)
    : list<(path_elem * 'a)> (* ↑ keys *) =
  let rec aux (bt: btree<'a>) (prefix: string) (acc: list<(path_elem * 'a)>) : list<(path_elem * 'a)> =
    match bt with
    | StrEmpty -> acc
    | StrBranch (k, v, lbt, rbt) ->
      let cmp = string_compare k prefix in
      let include_middle = BU.starts_with k prefix in
      let explore_right = cmp <= 0 || include_middle in
      let explore_left = cmp > 0 in
      let matches =
        if explore_right then aux rbt prefix acc else acc in
      let matches =
        if include_middle then
          ((Some prefix, k), v) :: matches
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

type name_collection<'a> =
| Names of btree<'a>
| ImportedNames of option<string> * names<'a>
and names<'a> = list<name_collection<'a>>

type trie<'a> =
| Trie of names<'a> (* bindings *) * namespaces<'a>
and namespaces<'a> = names<trie<'a>>

let trie_empty = Trie ([], [])

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
    match tr with
    | Trie (bindings, namespaces) ->
      BU.bind_opt (names_find_exact namespaces ns)
        (fun scope -> trie_descend_exact scope query)

let rec trie_descend_exact_error (tr: trie<'a>) (query: query) : trie<'a> =
  match trie_descend_exact tr query with
  | Some t -> t
  | None -> failwith (BU.format1 "Unknown module: %s" (String.concat "." query))

let names_insert (names: names<'a>) (id: string) (v: 'a) : names<'a> =
  let bt, names =
    match names with
    | Names bt :: tl -> (bt, tl)
    | _ -> (StrEmpty, names) in
  Names (btree_insert_replace bt id v) :: names

let rec namespaces_mutate (namespaces: namespaces<'a>) (ns: string)
                          (query: query) (mutator: trie<'a> -> trie<'a>) =
  let trie = BU.dflt trie_empty (names_find_exact namespaces ns) in
  names_insert namespaces ns (trie_mutate trie query mutator)

and trie_mutate (tr: trie<'a>) (query: query) (mutator: trie<'a> -> trie<'a>) : trie<'a> =
  match query with
  | [] -> mutator tr
  | id :: query ->
    match tr with
    | Trie (bindings, namespaces) ->
      Trie (bindings, namespaces_mutate namespaces id query mutator)

let trie_insert (tr: trie<'a>) (ns_query: query) (id: string) (v: 'a) : trie<'a> =
  trie_mutate tr ns_query (function
    | Trie (bindings, namespaces) -> Trie (names_insert bindings id v, namespaces))

let trie_include (tr: trie<'a>) (id: option<string>)
                 (host_query: query) (included_query: query)
    : trie<'a> =
  match trie_descend_exact_error tr included_query with
  | Trie (included_bindings, _) ->
    trie_mutate tr host_query (function
      | Trie (bindings, namespaces) ->
        Trie (ImportedNames (id, included_bindings) :: bindings, namespaces))

let trie_open_namespace (tr: trie<'a>) (id: string)
                        (host_query: query) (included_query: query)
    : trie<'a> =
  match trie_descend_exact_error tr included_query with
  | Trie (_, included_namespaces) ->
    trie_mutate tr host_query (function
      | Trie (bindings, namespaces) ->
        Trie (bindings, ImportedNames (Some id, included_namespaces) :: namespaces))

let trie_add_alias (tr: trie<'a>) (key: string)
                   (host_query: query) (included_query: query) : trie<'a> =
  match trie_descend_exact_error tr included_query with
  | Trie (included_bindings, _) ->
    trie_mutate tr host_query (fun tr ->
      // Very similar to an include, but aliasing A.B as M in A.C entirely
      // overrides A.B.M, should that also exists.  Doing this makes sense
      // because we only process aliases in the current module.
      trie_mutate tr [key] (function
        | _ignored_overwritten_trie ->
          Trie ([ImportedNames (None, included_bindings)], [])))

let names_revmap (fn: btree<'a> -> 'b)
                 (names: names<'a> (* ↓ priority *))
    : list<'b> (* ↑ priority *) =
  let rec aux (acc: list<'b>) (names: names<'a>) =
    List.fold_left (fun acc -> function
        | Names bt -> fn bt :: acc
        | ImportedNames (_, names) -> aux acc names)
      acc names in
  aux [] names

let btree_find_all (bt: btree<'a>) : list<(path_elem * 'a)> (* ↑ keys *) =
  btree_fold bt (fun k tr acc -> ((None, k), tr) :: acc) []

let names_find_prefix_rev (names: names<'a>) (id: option<string>) : list<(path_elem * 'a)> =
  let matching_values_per_collection =
    match id with
    | None -> names_revmap btree_find_all names
    | Some id -> names_revmap (fun bt -> btree_find_prefix bt id) names in
  merge_increasing_lists_rev
    (fun (path_el, _) -> snd path_el) matching_values_per_collection

let rec trie_find_prefix' (tr: trie<'a>) (path_acc: path)
                          (query: query) (acc: list<(path * 'a)>)
    : list<(path * 'a)> =
  // printf "\n<<<\n!! %A\n!! %A\n!! %A\n!! %A\n>>>\n\n" tr path_acc query acc;
  match tr with
  | Trie (bindings, namespaces) (* ↓ priority *) ->
    let ns_prefix, bindings_prefix, query =
      match query with
      | [] -> None, None, []
      | [id] -> Some id, Some id, []
      | ns :: query -> Some ns, None, query in

    let matching_namespaces_rev = names_find_prefix_rev namespaces ns_prefix in
    let acc_with_recursive_bindings =
      List.fold_left (fun acc (path_el, trie) ->
          trie_find_prefix' trie (path_el :: path_acc) query acc)
        acc matching_namespaces_rev in

    let matching_bindings_rev = names_find_prefix_rev bindings bindings_prefix in
    List.rev_map_onto (fun (path_el, v) -> (path_el :: path_acc, v))
      matching_bindings_rev acc_with_recursive_bindings

let trie_find_prefix (tr: trie<'a>) (query: query) : list<(path * 'a)> =
  List.map (fun (path_rev, v) -> (List.rev path_rev, v))
    (trie_find_prefix' tr [] query [])

(** * High level interface * **)

let test_trie =
  let tmp = trie_empty in

  let tmp = trie_insert tmp ["FStar"; "All"] "aaa" "FStar/All/aaa" in
  let tmp = trie_insert tmp ["FStar"; "All"] "bbb" "FStar/All/bbb" in
  let tmp = trie_insert tmp ["FStar"; "All"] "ccc" "FStar/All/ccc" in
  let tmp = trie_insert tmp ["Prims"] "xxx" "Prims/xxx" in
  let tmp = trie_insert tmp ["Prims"] "yyy" "Prims/yyy" in
  let tmp = trie_insert tmp ["Prims"] "zzz" "Prims/zzz" in
  let tmp = trie_include tmp None [] ["Prims"] in
  let tmp = trie_add_alias tmp "MyPrims" [] ["Prims"] in
  let tmp = trie_include tmp None ["FStar"; "All2"] ["FStar"; "All"] in
  // printf "exact: %A\n" (trie_find_exact tmp ["AA"; "B"]);
  // printf "exact w/ alias: %A\n" (trie_find_exact tmp ["XX"; "x"]);
  printf "prefix 1: %A\n" (trie_find_prefix tmp ["FSt"; "A"]);
  printf "prefix 2: %A\n" (trie_find_prefix tmp ["Prim"]);
  printf "prefix w/ alias: %A\n" (trie_find_prefix tmp ["X"]);
  // printf "flat: %A\n" (trie_flatten tmp [] []);
  printf "flat using prefix: %A\n" (trie_find_prefix tmp [""]);
  printf "full: %A\n" tmp;

  // let tmp = trie_insert tmp ["AA1"] "b1" "AA1/b1" in
  // let tmp = trie_insert tmp ["AA1"; "B1"] "C1" "AA1/B1/C1" in
  // let tmp = trie_insert tmp ["AA1"; "B1"] "D2" "AA1/B1/D2" in
  // let tmp = trie_insert tmp ["AA2"; "B1"] "C1" "AA2/B1/C1" in
  // let tmp = trie_insert tmp ["AA2"; "B1"] "D2" "AA2/B1/D2" in
  // let tmp = trie_insert tmp ["AB1"; "B1"] "C1" "AB1/B1/C1" in
  // let tmp = trie_insert tmp ["AB1"; "B1"] "D2" "AB1/B1/D2" in
  // // printf "exact: %A\n" (trie_find_exact tmp ["AA1"; "b1"]);
  // printf "prefix: %A\n" (trie_find_prefix tmp ["AA"; "b1"]);
  // printf "prefix: %A\n" (trie_find_prefix tmp ["AA"; "B"; ""])
  // // printf "flat: %A\n" (trie_flatten tmp [] [])

type symbol =
| Lid of Ident.lid

type table = trie<symbol>

let empty : table =
  trie_empty

let insert (tbl: table) (host_query: query) (id: string) (c: symbol) : table =
  trie_insert tbl host_query id c

let register_alias (tbl: table) (key: string) (host_query: query) (included_query: query) : table =
  trie_add_alias tbl key host_query included_query

let register_open (tbl: table) (is_module: bool) (host_query: query) (included_query: query) : table =
  let label = String.concat "." host_query in
  if is_module then
    trie_include tbl (Some label) host_query included_query
  else
    trie_open_namespace tbl label host_query included_query

let register_include (tbl: table) (host_query: query) (included_query: query) : table =
  trie_include tbl None host_query included_query

let path_match_length (path: path) : int =
  let length, (last_prefix, last_completion_length) =
    List.fold_left
      (fun acc elem ->
         let (acc_len, _) = acc in
         let (prefix_opt, completion) = elem in
         match prefix_opt with
         | Some prefix ->
           let completion_len = String.length completion in
           (acc_len + 1 (* ‘.’ *) + completion_len, (prefix, completion_len))
         | None -> acc)
      (0, ("", 0)) path in
  length
  - 1 (* extra ‘.’ *)
  - last_completion_length
  + (String.length last_prefix) (* match stops after last prefix *)

let path_to_string (path: path) : string =
  String.concat "." (List.map snd path)

type completion_result =
  { completion_kind: string;
    completion_match_length: int;
    completion_candidate: string;
    completion_annotation: string }

let make_result annotation (path: path) (symb: symbol) =
  match symb with
  | Lid l ->
    { completion_kind = "lid";
      completion_match_length = path_match_length path;
      completion_candidate = path_to_string path;
      completion_annotation = annotation }

let autocomplete (tbl: table) (query: query) =
  List.fold_left
    (fun acc (path, symb) -> make_result "" (* FIXME *) path symb :: acc)
    [] (trie_find_prefix tbl query)
