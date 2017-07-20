module FStar.Interactive.Completion

(** * Binary trees * **)

type btree<'a> =
| StrEmpty
| StrBranch of string * 'a * (btree<'a>) * (btree<'a>)
(* (key: string) * (value: 'a) * (ltr: btree 'a) * (rtr: btree 'a) *)

let starts_with (s1:string) (s2:string) = s1.StartsWith(s2)

let dflt x = function
    | None   -> x
    | Some x -> x

let bind_opt opt f =
    match opt with
    | None -> None
    | Some x -> f x

let map_option f opt = Option.map f opt

type lid = list<string>

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

let rec btree_find_prefix (tr: btree<'a>) (prefix: string) : list<string*'a> =
  let rec aux (tr: btree<'a>) (prefix: string) (acc: list<string*'a>) : list<string*'a> =
    match tr with
    | StrEmpty -> acc
    | StrBranch (k, v, ltr, rtr) ->
      let cmp = compare k prefix in
      let include_middle = starts_with k prefix in
      let explore_left = cmp > 0 in
      let explore_right = cmp <= 0 || include_middle in
      let matches = if explore_right then aux rtr prefix acc else acc in
      let matches = if include_middle then (k, v) :: matches else matches in
      let matches = if explore_left then aux ltr prefix matches else matches in
      matches in
  aux tr prefix []

let rec btree_fold (tr: btree<'a>) (f: string -> 'a -> 'b -> 'b) (acc: 'b) =
  match tr with
  | StrEmpty -> acc
  | StrBranch (k, v, ltr, rtr) ->
    btree_fold ltr f (f k v (btree_fold rtr f acc))

(** * Tries * **)

type path = list<string>

type subtrie<'a> =
| Alias of string * path
| ProperSubtrie of trie<'a>
and trie<'a> =
| Trie of option<'a> * btree<subtrie<'a>>

let trie_empty = Trie (None, StrEmpty)
let subtrie_empty = ProperSubtrie trie_empty

type result<'a> = path*'a
type oresult<'a> = option<result<'a>>

let extend_result_path (prefix: string) (pth, res) : result<'a> =
  (prefix :: pth, res)

let rec trie_descend_exact (pth: path) (tr: trie<'a>) : option<trie<'a>> =
  match pth with
  | [] -> Some tr
  | id :: pth ->
    match tr with
    | Trie (vopt, subtries) ->
      bind_opt (btree_find_trie_exact subtries id)
        (fun subtrie -> trie_descend_exact pth subtrie)

and resolve_subtrie_aliases (tr: btree<subtrie<'a>>) (k: string) (subtrie: subtrie<'a>) : option<trie<'a>> =
  match subtrie with
  | Alias (hd, tl) ->
    bind_opt (btree_find_trie_exact tr hd)
      (fun tr' -> trie_descend_exact tl tr')
  | ProperSubtrie st -> Some st

and btree_find_trie_exact (tr: btree<subtrie<'a>>) (k: string) : option<trie<'a>> =
  bind_opt (btree_find_exact tr k) (resolve_subtrie_aliases tr k)

let trie_find_exact (pth: path) (tr: trie<'a>) : option<'a> =
  bind_opt (trie_descend_exact pth tr)
    (function | Trie (vopt, _) -> vopt)

let trie_insert (tr: trie<'a>) (pth: path) (v: 'a) : trie<'a> =
  let rec aux pth tr =
    match tr with
    | Trie (vopt, subtries) ->
      match pth with
      | [] ->
        Trie (Some v, subtries)
      | id :: pth ->
        match dflt subtrie_empty (btree_find_exact subtries id) with
        | Alias _ -> failwith "Inserting under module alias"
        | ProperSubtrie subtrie ->
          Trie (vopt, btree_insert subtries id (ProperSubtrie (aux pth subtrie))) in
  aux pth tr

let rec trie_flatten (rev_path_prefix: path) (tr: trie<'a>) (acc: list<result<'a>>) =
  match tr with
  | Trie (vopt, subtries) ->
    let helper k subtr acc =
      match resolve_subtrie_aliases subtries k subtr with
      | None -> acc
      | Some subtrie -> trie_flatten (k :: rev_path_prefix) subtrie acc in
    let acc = btree_fold subtries helper acc in
    match vopt with
    | None -> acc
    | Some v -> (List.rev rev_path_prefix, v) :: acc

let trie_find_prefix (pth: path) (tr: trie<'a>) =
  let rec aux (rev_path_prefix: path) (pth: path) (tr: trie<'a>) (acc: list<result<'a>>) =
    match pth with
    | [] -> trie_flatten rev_path_prefix tr acc
    | id :: pth ->
      match tr with
      | Trie (vopt, subtries) ->
        let matching_subtries : list<string*subtrie<'a>> = btree_find_prefix subtries id in
        List.foldBack (fun (complete_id, subtr) acc ->
                       match resolve_subtrie_aliases subtries id subtr with
                       | None -> acc
                       | Some subtrie ->
                         aux (complete_id :: rev_path_prefix) pth subtrie acc)
                      matching_subtries acc in
  aux [] pth tr []

let trie_add_alias (tr: trie<'a>) key path =
  match path with
  | [] -> failwith "Can't alias to an empty path."
  | h :: t ->
    match tr with
    | Trie (vopt, subtries) ->
      Trie (vopt, btree_insert subtries key (Alias (h, t)))

(** * High level interface * **)

let full =
 Trie (None,
   StrBranch
     ("AA",
      ProperSubtrie
        (Trie
           (None,
            StrBranch
              ("B",ProperSubtrie (Trie (Some "AA/B",StrEmpty)),StrEmpty,
               StrBranch
                 ("C1",ProperSubtrie (Trie (Some "AA/C1",StrEmpty)),StrEmpty,
                  StrBranch
                    ("C2",ProperSubtrie (Trie (Some "AA/C2",StrEmpty)),StrEmpty,
                     StrEmpty))))),StrEmpty,StrEmpty))

let _ =
    let tmp = trie_empty in

    let tmp = trie_insert tmp ["AA"; "B"] "AA/B" in
    let tmp = trie_insert tmp ["AA"; "C1"] "AA/C1" in
    let tmp = trie_insert tmp ["AA"; "C2"; "x"] "AA/C2/x" in
    let tmp = trie_add_alias tmp "XX" ["AA"; "C2"] in
    printf "exact: %A\n" (trie_find_exact ["AA"; "B"] tmp);
    printf "exact w/ alias: %A\n" (trie_find_exact ["XX"; "x"] tmp);
    printf "prefix 1: %A\n" (trie_find_prefix ["AA"; ""] tmp);
    printf "prefix 2: %A\n" (trie_find_prefix ["A"; "C2"] tmp);
    printf "prefix w/ alias: %A\n" (trie_find_prefix ["X"] tmp);
    printf "flat: %A\n" (trie_flatten [] tmp []);
    // printf "full: %A\n" tmp;

    // let tmp = trie_insert tmp ["AA1"; "b1"] "AA1/b1" in
    // let tmp = trie_insert tmp ["AA1"; "B1"; "C1"] "AA1/B1/C1" in
    // let tmp = trie_insert tmp ["AA1"; "B1"; "D2"] "AA1/B1/C2" in
    // let tmp = trie_insert tmp ["AA2"; "B1"; "C1"] "AA2/B1/C1" in
    // let tmp = trie_insert tmp ["AA2"; "B1"; "D2"] "AA2/B1/C2" in
    // let tmp = trie_insert tmp ["AB1"; "B1"; "C1"] "AB1/B1/C1" in
    // let tmp = trie_insert tmp ["AB1"; "B1"; "D2"] "AB1/B1/C2" in
    // printf "exact: %A\n" (trie_find_exact ["AA1"; "b1"] tmp);
    // printf "prefix: %A\n" (trie_find_prefix ["AA"; "b1"] tmp);
    // printf "prefix: %A\n" (trie_find_prefix ["AA"; "B"; ""] tmp);
    // printf "flat: %A\n" (trie_flatten tmp [])

type candidate =
| Lid of lid

let pth_of_candidate (c: candidate) =
  match c with
  | Lid l -> List.map FStar.Ident.text_of_id (FStar.Ident.ids_of_lid l)

type table = trie<candidate>

let empty : table =
  trie_empty

let insert (tbl: table) (c: candidate) =
  let pth = pth_of_candidate c in
  trie_insert tbl pth c

let autocomplete = 1
