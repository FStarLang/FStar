#light "off"
module FStar.Interactive.CompletionTable

open FStar
module BU = Util

(** * List functions * **)

let rec merge_2_decreasing_lists_rev l1 l2 (size, acc) =
  match l1, l2 with
  | l, []
  | [], l ->
    (size + List.length l), List.rev_append l acc
  | (k1, v1) :: t1, (k2, v2) :: t2 ->
    let cmp = String.compare k1 k2 in
    if cmp < 0 then
      merge_2_decreasing_lists_rev l1 t2 (1 + size, (k2, v2) :: acc)
    else if cmp > 0 then
      merge_2_decreasing_lists_rev t1 l2 (1 + size, (k1, v1) :: acc)
    else // Drop duplicates found in ‘l1’
      merge_2_decreasing_lists_rev t1 l2 (size, acc)

(** Merge ‘lists’, a list of decreasing (according to ‘key_fn’) lists.
    Keeps a single copy of each key that appears in more than one list (later
    lists take precedence when chosing which value to keep). *)
let rec merge_decreasing_lists_rev
    (key_fn: 'a -> string) (lists: list<list<'a>>) (acc: list<'a>) =
  (** Find the largest key in [List.map List.hd lists] and the associated value.
      When multiple keys are equal, keep the value from the latest occurence. *)
  let rec find_max lists =
    match lists with
    | [] -> None
    | [] :: t -> find_max t
    | (v :: _) :: t ->
      let k = key_fn v in
      match find_max t with
      | None ->
        Some (k, v)
      | Some (k', v') ->
        Some (if String.compare k k' > 0 then (k, v) else (k', v')) in
  (** Filter ‘lists’, removing empties and dropping heads whose key is ‘k0’. *)
  let rec pop k0 lists =
    List.filter_map (fun ls ->
                       match ls with
                       | [] -> None
                       | h :: t -> Some (if key_fn h = k0 then t else ls))
                    lists in
  match find_max lists with
  | None -> acc
  | Some mx -> merge_decreasing_lists_rev key_fn (pop (fst mx) lists) ((snd mx) :: acc)

(** * Binary trees * **)

type btree<'a> =
| StrEmpty
| StrBranch of string * 'a * (btree<'a>) * (btree<'a>)
(* (key: string) * (value: 'a) * (ltr: btree 'a) * (rtr: btree 'a) *)

let rec btree_to_list_rev btree acc =
  match btree with
  | StrEmpty -> acc
  | StrBranch (key, value, ltr, rtr) ->
    btree_to_list_rev rtr ((key, value) :: btree_to_list_rev ltr acc)

let rec btree_from_list nodes size =
  if size = 0 then (StrEmpty, nodes)
  else
    let ltr_size = size / 2 in
    let rtr_size = size - ltr_size - 1 in
    let ltr, nodes_left = btree_from_list nodes ltr_size in
    match nodes_left with
    | [] -> failwith "Invalid size passed to btree_from_list"
    | (k, v) :: nodes_left ->
      let rtr, nodes_left = btree_from_list nodes_left rtr_size in
      StrBranch (k, v, ltr, rtr), nodes_left

let btree_merge tr1 tr2 =
  printf "Merging btrees:\n>1> %A\n>2> %A\n"
    (List.map fst (btree_to_list_rev tr1 []))
    (List.map fst (btree_to_list_rev tr2 []));
  let size, nodes =
    merge_2_decreasing_lists_rev
      (btree_to_list_rev tr1 [])
      (btree_to_list_rev tr2 [])
      (0, []) in
  fst (btree_from_list nodes size)

let rec btree_insert (tr: btree<'a>) (k: string) (v: 'a) : btree<'a> =
  match tr with
  | StrEmpty -> StrBranch (k, v, StrEmpty, StrEmpty)
  | StrBranch (k', v', ltr, rtr) ->
    let cmp = String.compare k k' in
    if cmp < 0 then
      StrBranch (k', v', btree_insert ltr k v, rtr)
    else if cmp > 0 then
      StrBranch (k', v', ltr, btree_insert rtr k v)
    else
      StrBranch (k', v, ltr, rtr)

let rec btree_find_exact (tr: btree<'a>) (k: string) : option<'a> =
  match tr with
  | StrEmpty -> None
  | StrBranch (k', v, ltr, rtr) ->
    let cmp = String.compare k k' in
    if cmp < 0 then
      btree_find_exact ltr k
    else if cmp > 0 then
      btree_find_exact rtr k
    else
      Some v

type path_elem = option<string>*string

let rec btree_find_prefix (tr: btree<'a>) (prefix: string) : list<path_elem*'a> =
  let rec aux (tr: btree<'a>) (prefix: string) (acc: list<path_elem*'a>) : list<path_elem*'a> =
    match tr with
    | StrEmpty -> acc
    | StrBranch (k, v, ltr, rtr) ->
      let cmp = String.compare k prefix in
      let include_middle = BU.starts_with k prefix in
      let explore_right = cmp <= 0 || include_middle in
      let explore_left = cmp > 0 in
      let matches =
        if explore_right then aux rtr prefix acc else acc in
      let matches =
        if include_middle then
          ((Some prefix, k), v) :: matches
        else
          matches in
      let matches =
        if explore_left then aux ltr prefix matches else matches in
      matches in
  aux tr prefix []

let rec btree_fold (tr: btree<'a>) (f: string -> 'a -> 'b -> 'b) (acc: 'b) =
  match tr with
  | StrEmpty -> acc
  | StrBranch (k, v, ltr, rtr) ->
    btree_fold ltr f (f k v (btree_fold rtr f acc))

(** * Tries * **)

type path = list<path_elem>
type query = list<string>

type subtrie<'a> =
| Alias of string * query
| ProperSubtrie of trie<'a>
and trie<'a> =
| Trie of option<'a> * btree<subtrie<'a>>

let trie_empty = Trie (None, StrEmpty)
let subtrie_empty = ProperSubtrie trie_empty

let rec trie_descend_exact (tr: trie<'a>) (query: query) : option<trie<'a>> =
  match query with
  | [] -> Some tr
  | id :: query ->
    match tr with
    | Trie (vopt, subtries) ->
      BU.bind_opt (btree_find_trie_exact subtries id)
        (fun subtrie -> trie_descend_exact subtrie query)

and resolve_subtrie_aliases (tr: btree<subtrie<'a>>) (k: string) (subtrie: subtrie<'a>) : option<trie<'a>> =
  match subtrie with
  | Alias (hd, tl) ->
    BU.bind_opt (btree_find_trie_exact tr hd)
      (fun tr' -> trie_descend_exact tr' tl)
  | ProperSubtrie st -> Some st

and btree_find_trie_exact (tr: btree<subtrie<'a>>) (k: string) : option<trie<'a>> =
  BU.bind_opt (btree_find_exact tr k) (resolve_subtrie_aliases tr k)

let trie_find_exact (tr: trie<'a>) (query: query) : option<'a> =
  BU.bind_opt (trie_descend_exact tr query)
    (function | Trie (vopt, _) -> vopt)

let trie_mutate (tr: trie<'a>) (query: query) (mutator: trie<'a> -> trie<'a>) : trie<'a> =
  let rec aux query tr =
    match query with
    | [] ->
      mutator tr
    | id :: query ->
      match tr with
      | Trie (vopt, subtries) ->
        match BU.dflt subtrie_empty (btree_find_exact subtries id) with
        | Alias _ -> failwith "Mutating under module alias"
        | ProperSubtrie subtrie ->
          Trie (vopt, btree_insert subtries id (ProperSubtrie (aux query subtrie))) in
  aux query tr

let trie_insert (tr: trie<'a>) (query: query) (v: 'a) : trie<'a> =
  trie_mutate tr query (function | Trie (_, subtries) -> Trie (Some v, subtries))

// FIXME:
// * Does include also import aliases?
// * Is include recursive?
// * Is this merging approach fast enough?
//   If not, it should be possible to replace the list of btrees in the the type
//   of ‘trie’ with a heterogeneous list of btrees (local definitions) and tries
//   (includes).
let trie_merge (tr: trie<'a>) (host_query: query) (subtries: btree<subtrie<'a>>) : trie<'a> =
  trie_mutate tr host_query (function
    | Trie (vopt, prev_subtries) -> // ‘subtries’ shadows ‘prev_subtries’
      Trie (vopt, btree_merge prev_subtries subtries))

let rec trie_flatten (tr: trie<'a>) (rev_path_prefix: path) (acc: list<path*'a>) =
  match tr with
  | Trie (vopt, subtries) ->
    let helper k subtr acc =
      match resolve_subtrie_aliases subtries k subtr with
      | None -> acc
      | Some subtrie -> trie_flatten subtrie ((None, k) :: rev_path_prefix) acc in
    let acc = btree_fold subtries helper acc in
    match vopt with
    | None -> acc
    | Some v -> (List.rev rev_path_prefix, v) :: acc

let trie_find_prefix (tr: trie<'a>) (query: query) =
  let rec aux (rev_path_prefix: path) (query: query) (tr: trie<'a>) (acc: list<path*'a>) =
    match query with
    | [] -> trie_flatten tr rev_path_prefix acc
    | id :: query ->
      match tr with
      | Trie (vopt, subtries) ->
        let matching_subtries = btree_find_prefix subtries id in
        List.fold_right
          (fun (complete_id, subtr) acc ->
             match resolve_subtrie_aliases subtries id subtr with
             | None -> acc
             | Some subtrie ->
               aux (complete_id :: rev_path_prefix) query subtrie acc)
          matching_subtries acc in
  aux [] query tr []

let trie_add_alias (tr: trie<'a>) key path =
  match path with
  | [] -> failwith "Can't alias to an empty path."
  | h :: t ->
    match tr with
    | Trie (vopt, subtries) ->
      Trie (vopt, btree_insert subtries key (Alias (h, t)))

(** * High level interface * **)

let test () =
    let tmp = trie_empty in

    let tmp = trie_insert tmp ["AA"; "B"] "AA/B" in
    let tmp = trie_insert tmp ["AA"; "C1"] "AA/C1" in
    let tmp = trie_insert tmp ["AA"; "C2"; "x"] "AA/C2/x" in
    let tmp = trie_add_alias tmp "XX" ["AA"; "C2"] in
    printf "exact: %A\n" (trie_find_exact tmp ["AA"; "B"]);
    printf "exact w/ alias: %A\n" (trie_find_exact tmp ["XX"; "x"]);
    printf "prefix 1: %A\n" (trie_find_prefix tmp ["AA"; ""]);
    printf "prefix 2: %A\n" (trie_find_prefix tmp ["A"; "C2"]);
    printf "prefix w/ alias: %A\n" (trie_find_prefix tmp ["X"]);
    printf "flat: %A\n" (trie_flatten tmp [] []);
    printf "flat using prefix: %A\n" (trie_find_prefix tmp []);
    printf "flat using prefix (2): %A\n" (trie_find_prefix tmp [""]);
    // printf "full: %A\n" tmp;

    let tmp = trie_insert tmp ["AA1"; "b1"] "AA1/b1" in
    let tmp = trie_insert tmp ["AA1"; "B1"; "C1"] "AA1/B1/C1" in
    let tmp = trie_insert tmp ["AA1"; "B1"; "D2"] "AA1/B1/C2" in
    let tmp = trie_insert tmp ["AA2"; "B1"; "C1"] "AA2/B1/C1" in
    let tmp = trie_insert tmp ["AA2"; "B1"; "D2"] "AA2/B1/C2" in
    let tmp = trie_insert tmp ["AB1"; "B1"; "C1"] "AB1/B1/C1" in
    let tmp = trie_insert tmp ["AB1"; "B1"; "D2"] "AB1/B1/C2" in
    printf "exact: %A\n" (trie_find_exact tmp ["AA1"; "b1"]);
    printf "prefix: %A\n" (trie_find_prefix tmp ["AA"; "b1"]);
    printf "prefix: %A\n" (trie_find_prefix tmp ["AA"; "B"; ""]);
    printf "flat: %A\n" (trie_flatten tmp [] [])

type symbol =
| Lid of Ident.lid

let query_of_symbol (c: symbol) =
  match c with
  | Lid l -> List.map Ident.text_of_id (Ident.ids_of_lid l)

type table = trie<symbol>

let empty : table =
  trie_empty

let insert (tbl: table) (c: symbol) : table =
  printf "Inserting %A\n" (query_of_symbol c);
  let query = query_of_symbol c in
  trie_insert tbl query c

let register_alias (tbl: table) (key: string) (query: query) : table =
  trie_add_alias tbl key query

let register_include (tbl: table) (host_query: query) (included_query: query) : table =
  match trie_descend_exact tbl included_query with
  | None -> printf "%A\n" tbl; failwith (Util.format1 "Including an unknown module (%s)"
                       (String.concat "." included_query))
  | Some (Trie (_, included_subtries)) ->
    trie_merge tbl host_query included_subtries

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

let make_result (root_query: query) (path: path) (symb: symbol) =
  match symb with
  | Lid l ->
    { completion_kind = "lid";
      completion_match_length = path_match_length path;
      completion_candidate = path_to_string path;
      completion_annotation = String.concat "." root_query }

let autocomplete (tbl: table) (query: query) (root_queries: list<query>) =
  let result_sets : list<list<completion_result>> =
    List.fold_left
      (fun acc root_query ->
         match trie_descend_exact tbl root_query with
         | None -> acc
         | Some root ->
           let results =
             List.fold_left
               (fun acc (path, symb) -> make_result root_query path symb :: acc)
               [] (trie_find_prefix root query) in
           results :: acc)
      [] root_queries in
  merge_decreasing_lists_rev (fun res -> res.completion_candidate) result_sets []
