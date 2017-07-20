#light "off"
module FStar.Interactive.Completion

module BU = FStar.Util

(** * Binary trees * **)

type btree<'a> =
| StrEmpty
| StrBranch of string * 'a * (btree<'a>) * (btree<'a>)
(* (key: string) * (value: 'a) * (ltr: btree 'a) * (rtr: btree 'a) *)

let rec btree_insert (tr: btree<'a>) (k: string) (v: 'a) : btree<'a> =
  match tr with
  | StrEmpty -> StrBranch (k, v, StrEmpty, StrEmpty)
  | StrBranch (k', v', ltr, rtr) ->
    let cmp = compare k k' in
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
    let cmp = compare k k' in
    if cmp < 0 then
      btree_find_exact ltr k
    else if cmp > 0 then
      btree_find_exact rtr k
    else
      Some v

type path_elem = option<int>*string

let rec btree_find_prefix (tr: btree<'a>) (prefix: string) : list<path_elem*'a> =
  let rec aux (tr: btree<'a>) (prefix: string) (acc: list<path_elem*'a>) : list<path_elem*'a> =
    match tr with
    | StrEmpty -> acc
    | StrBranch (k, v, ltr, rtr) ->
      let cmp = compare k prefix in
      let include_middle = BU.starts_with k prefix in
      let explore_right = cmp <= 0 || include_middle in
      let explore_left = cmp > 0 in
      let matches =
        if explore_right then aux rtr prefix acc else acc in
      let matches =
        if include_middle then
          ((Some (String.length prefix), k), v) :: matches
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

let trie_insert (tr: trie<'a>) (query: query) (v: 'a) : trie<'a> =
  let rec aux query tr =
    match tr with
    | Trie (vopt, subtries) ->
      match query with
      | [] ->
        Trie (Some v, subtries)
      | id :: query ->
        match BU.dflt subtrie_empty (btree_find_exact subtries id) with
        | Alias _ -> failwith "Inserting under module alias"
        | ProperSubtrie subtrie ->
          Trie (vopt, btree_insert subtries id (ProperSubtrie (aux query subtrie))) in
  aux query tr

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
        List.foldBack (fun (complete_id, subtr) acc ->
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

let _ =
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
| Lid of FStar.Ident.lid

let query_of_symbol (c: symbol) =
  match c with
  | Lid l -> List.map FStar.Ident.text_of_id (FStar.Ident.ids_of_lid l)

type table = trie<symbol>

let empty : table =
  trie_empty

let insert (tbl: table) (c: symbol) : table =
  let query = query_of_symbol c in
  trie_insert tbl query c

let register_alias (tbl: table) (key: string) (query: query) : table =
  trie_add_alias tbl key query

let path_match_length (path: path) : int =
  List.fold (fun acc elem ->
             match fst elem with
             | Some nchars -> 1 (* ‘.’ *) + nchars + acc
             | None -> acc)
            0 path

let path_to_string (path: path) : string =
  String.concat "." (List.map snd path)

type completion_result =
  { completion_kind: string;
    completion_match_length: int;
    completion_candidate: string;
    completion_annotation: string }

let make_completion_result (root_query: query) (path: path) (symb: symbol) =
  match symb with
  | Lid l ->
    { completion_kind = "lid";
      completion_match_length = path_match_length path;
      completion_candidate = path_to_string path;
      completion_annotation = String.concat "." root_query }

let autocomplete (tbl: table) (query: query) =
  let results = trie_find_prefix tbl query in
  List.map (fun (path, symb) -> make_completion_result [] path symb) results
