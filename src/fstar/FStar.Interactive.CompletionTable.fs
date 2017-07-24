// -*- fstar-subp-prover-args: ("--eager_inference" "--lax" "--MLish" "--include" "../../ulib" "--include" "../u_boot_fsts" "--include" "../boot_fstis") -*-

#light "off"
module FStar.Interactive.CompletionTable

open FStar
open FStar.All
module BU = FStar.Util

// module String = begin
//   let compare = compare
// end

// module List = begin
//     let filter_map f l =
//         (let rec filter_map acc l =
//            match l with
//            | [] ->
//                List.rev acc
//            | hd :: tl ->
//                match f hd with
//                | Some hd ->
//                    filter_map (hd :: acc) tl
//                | None ->
//                    filter_map acc tl
//          in
//          filter_map [] l)

//      let fold_left = List.fold

//      let rec rev_acc = (fun ( l  :  'a list ) ( acc  :  'a list ) ->
//                         (match (l) with
//                          | [] -> begin
//                                     acc
//                                 end
//                          | hd::tl -> begin
//                                        (rev_acc tl ((hd)::acc))
//                                    end))

//      let rev_append l a = rev_acc l a
//   end
// module All = begin end
// module BU = begin
//     let bind_opt opt f =
//         match opt with
//         | None -> None
//         | Some x -> f x
//     let dflt x = function
//         | None   -> x
//         | Some x -> x
//     let format1 msg arg = msg ^ arg
//     let starts_with = fun (s: string) pref -> s.StartsWith pref
// end

// module List = begin
//   let fold_left = List.fold
//   let hd = List.head
// end

// module String = begin
//   let compare = compare
//   let uppercase (s: string) = s.ToUpperInvariant ()
// end

let string_compare s1 s2 =
  String.compare s1 s2 // (String.uppercase s1) (String.uppercase s2)

(** * (Pairing) max-heaps * **)

type heap<'a> =
| EmptyHeap
| Heap of 'a * list<heap<'a>>

let heap_merge cmp h1 h2 =
  match h1, h2 with
  | EmptyHeap, h
  | h, EmptyHeap -> h
  | Heap (v1, hh1), Heap (v2, hh2) ->
    if cmp v1 v2 > 0 then Heap (v1, h2 :: hh1) else Heap (v2, h1 :: hh2)

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

(** Merge ‘lists’, a list of decreasing (according to ‘key_fn’) lists.
    Keeps a single copy of each key that appears in more than one list (earlier
    lists take precedence when chosing which value to keep). *)
let merge_decreasing_lists_rev (key_fn: 'a -> string) (lists: list<list<'a>>) =
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
  let lists = add_priorities 0 [] lists in
  aux (heap_from_list cmp lists) []

let test_merge () =
  let l1 = [("And", 7); ("admitP", 5); ("2", 2); ("1", 1)] in
  let l2 = [("And", 77); ("admitP", 66); ("5", 55); ("3", 3); ("1", 1)] in
  let l3 = [("And", 777); ("admitP", 555); ("4", 4); ("1", 1)] in
  merge_decreasing_lists_rev (fun (k, _) -> k) [l1;l2;l3]

// FIXME does this maintain order?

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

let rec btree_insert (bt: btree<'a>) (k: string) (v: 'a) : btree<'a> =
  match bt with
  | StrEmpty -> StrBranch (k, v, StrEmpty, StrEmpty)
  | StrBranch (k', v', lbt, rbt) ->
    let cmp = string_compare k k' in
    if cmp < 0 then
      StrBranch (k', v', btree_insert lbt k v, rbt)
    else if cmp > 0 then
      StrBranch (k', v', lbt, btree_insert rbt k v)
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

let rec btree_find_prefix (bt: btree<'a>) (prefix: string) : list<(path_elem * 'a)> =
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

type scope<'a> =
| Bindings of btree<trie<'a>>
| Alias of list<scope<'a>>
| Include of list<scope<'a>>
| Use of (* Module *) string * list<scope<'a>>
| Open of (* Namespace *) string * list<scope<'a>>
and trie<'a> =
| Trie of option<'a> * (* reversed list of scopes *) list<scope<'a>>

let trie_empty = Trie (None, [])

// TODO: scopes_find_exact and trie_descend_exact are over-approximations: they
// should take an extra parameter in_incl.  Alternatively, they could be
// tightened to only inspect Bindings.

let rec scopes_find_exact (scopes: list<scope<'a>>) (id: string) : option<trie<'a>> =
  let result, scopes =
    match scopes with
    | [] ->
      None, None
    | Bindings bt :: scopes ->
      btree_find_exact bt id, Some scopes
    | Alias scopes :: more_scopes
    | Include scopes :: more_scopes
    | Use (_, scopes) :: more_scopes
    | Open (_, scopes) :: more_scopes ->
      scopes_find_exact scopes id, Some more_scopes in
  match result, scopes with
  | None, Some scopes -> scopes_find_exact scopes id
  | _ -> result

let rec trie_descend_exact (tr: trie<'a>) (query: query) : option<trie<'a>> =
  match query with
  | [] -> Some tr
  | id :: query ->
    match tr with
    | Trie (vopt, scopes) ->
      BU.bind_opt (scopes_find_exact scopes id)
        (fun scope -> trie_descend_exact scope query)

let trie_find_exact (tr: trie<'a>) (query: query) : option<'a> =
  BU.bind_opt (trie_descend_exact tr query)
    (function | Trie (vopt, _) -> vopt)

let scopes_insert (scopes: list<scope<'a>>) (id: string) (tr: trie<'a>) : list<scope<'a>> =
  let bt, scopes = match scopes with
                     | Bindings bt :: tl -> (bt, tl)
                     | _ -> (StrEmpty, scopes) in
  Bindings (btree_insert bt id tr) :: scopes

let rec scopes_mutate (scopes: list<scope<'a>>) (id: string) (query: list<string>) (mutator: trie<'a> -> trie<'a>) =
  let trie = BU.dflt trie_empty (scopes_find_exact scopes id) in
  scopes_insert scopes id (trie_mutate trie query mutator)

and trie_mutate (tr: trie<'a>) (query: query) (mutator: trie<'a> -> trie<'a>) : trie<'a> =
  match query with
  | [] ->
    mutator tr
  | id :: query ->
    match tr with
    | Trie (vopt, scopes) ->
      Trie (vopt, scopes_mutate scopes id query mutator)

let trie_insert (tr: trie<'a>) (query: query) (v: 'a) : trie<'a> =
  trie_mutate tr query (function | Trie (_, scopes) -> Trie (Some v, scopes))

let rec trie_descend_exact_error (tr: trie<'a>) (query: query) (message: string) : trie<'a> =
  match trie_descend_exact tr query with
  | Some t -> t
  | None -> failwith (BU.format1 message (String.concat "." query))

let trie_add_alias (tr: trie<'a>) (key: string) (host_query: query) (included_query) : trie<'a> =
  match trie_descend_exact_error tr included_query
          "Aliasing an unknown module (%s)" with
  | Trie (_, scopes) ->
    trie_mutate tr host_query (fun tr ->
      trie_mutate tr [key] (function
        | Trie (vopt, prev_scopes) -> Trie (vopt, [Alias scopes])))

let trie_include (tr: trie<'a>) (host_query: query) (included_query: query)
                 (wrapper: list<scope<'a>> -> scope<'a>) : trie<'a> =
  match trie_descend_exact_error tr included_query
          "Including an unknown module (%s)" with
  | Trie (_, scopes) ->
    trie_mutate tr host_query (function
      | Trie (vopt, prev_scopes) -> Trie (vopt, wrapper scopes :: prev_scopes))

let btree_find_all (bt: btree<'a>) : list<(path_elem * 'a)> =
  btree_fold bt (fun k tr acc -> ((None, k), tr) :: acc) []

let scopes_revmap (in_incl: bool)
                  (fn: btree<trie<'a>> -> 'b)
                  (scopes: list<scope<'a>>) : list<(bool * 'b)> =
  let rec aux (in_incl: bool) (acc: list<(bool * 'b)>) (scopes: list<scope<'a>>) =
    List.fold_left (fun acc scope ->
        match scope with
        | Bindings bt -> (in_incl, fn bt) :: acc
        | Include scopes -> aux true acc scopes
        | Alias scopes -> if in_incl then failwith "Alias in included file"
                         else aux true acc scopes
        | Use (_, scopes) -> if in_incl then failwith "Open module in included file"
                            else aux true (* Using a module is like including it *) acc scopes
        | Open (_, scopes) -> if in_incl then failwith "Open namespace in included file"
                             else aux false acc scopes)
      acc scopes in
  aux in_incl [] scopes

let rec scopes_find_prefix
    (in_incl: bool) (scopes: list<scope<'a>>) (query: query)
    (rev_path_prefix: path) (acc: list<(path * 'a)> (* ↓ alphabetically *)) =
  let btree_matcher, query =
    match query with
    | [] -> btree_find_all, []
    | id :: query -> (fun bt -> btree_find_prefix bt id), query in
  let matching_tries_per_scope_rev
      : list<(bool * list<(path_elem * trie<'a>)>)> (* ↑ by priority *) =
    scopes_revmap in_incl btree_matcher scopes in
  let candidates_per_scope : list<list<(path * 'a)>> (* ↓ by priority *) =
    List.map (fun (in_incl', tries (* ↑ alphabetically *)) ->
              let in_incl = in_incl || in_incl' in
              List.fold_left
                (fun acc (* ↓ alphabetically *) (completed_id, trie) ->
                   trie_find_prefix' in_incl trie query
                                     (completed_id :: rev_path_prefix) acc)
                [] tries)
             matching_tries_per_scope_rev in
  let key_fn = function
    | ((_, key) :: _, _) -> key
    | _ -> failwith "Empty path" in
  // printf "Merging lists: %A\n" (List.map (List.map key_fn) candidates_per_scope);
  List.rev_append (merge_decreasing_lists_rev key_fn candidates_per_scope) acc

and trie_find_prefix'
    (in_incl: bool) (tr: trie<'a>) (query: query)
    (rev_path_prefix: path) (acc: list<(path * 'a)> (* ↓ alphabetically *)) =
  match tr with
  | Trie (vopt, scopes (* ↓ by priority *)) ->
    let acc = if in_incl then acc
              else scopes_find_prefix in_incl scopes query rev_path_prefix acc in
    match vopt with
    | Some v when query = [] -> (rev_path_prefix, v) :: acc
    | _ -> acc

let trie_find_prefix_rev (tr: trie<'a>) (query: query) : list<(path * 'a)> =
  trie_find_prefix' false tr query [] []

let trie_find_prefix (tr: trie<'a>) (query: query) : list<(path * 'a)> =
  List.rev (trie_find_prefix_rev tr query)

(** * High level interface * **)

let test_trie () =
    let tmp = trie_empty in

    let tmp = trie_insert tmp ["AA"; "B"] "AA/B" in
    let tmp = trie_insert tmp ["AA"; "C1"] "AA/C1" in
    let tmp = trie_insert tmp ["AA"; "C2"; "x"] "AA/C2/x" in
    let tmp = trie_include tmp ["XX"] ["AA"; "C2"] Include in
    printf "exact: %A\n" (trie_find_exact tmp ["AA"; "B"]);
    printf "exact w/ alias: %A\n" (trie_find_exact tmp ["XX"; "x"]);
    printf "prefix 1: %A\n" (trie_find_prefix tmp ["AA"; ""]);
    printf "prefix 2: %A\n" (trie_find_prefix tmp ["A"; "C2"]);
    printf "prefix w/ alias: %A\n" (trie_find_prefix tmp ["X"]);
    // printf "flat: %A\n" (trie_flatten tmp [] []);
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
    printf "prefix: %A\n" (trie_find_prefix tmp ["AA"; "B"; ""])
    // printf "flat: %A\n" (trie_flatten tmp [] [])

type symbol =
| Lid of Ident.lid

type table = trie<symbol>

let empty : table =
  trie_empty

let insert (tbl: table) (query: query) (c: symbol) : table =
  trie_insert tbl query c

let register_alias (tbl: table) (key: string) (host_query: query) (included_query: query) : table =
  trie_add_alias tbl key host_query included_query

let register_open (tbl: table) (is_module: bool) (host_query: query) (included_query: query) : table =
  let label = String.concat "." host_query in
  let wrapper = if is_module then Use else Open in
  trie_include tbl host_query included_query (fun scopes -> wrapper (label, scopes))

let register_include (tbl: table) (host_query: query) (included_query: query) : table =
  trie_include tbl host_query included_query (fun scopes -> Include scopes)

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

let autocomplete (tbl: table) (query: query) =
  List.fold_left
    (fun acc (rev_path, symb) -> make_result [] (* FIXME *) (List.rev rev_path) symb :: acc)
    [] (trie_find_prefix_rev tbl query)
