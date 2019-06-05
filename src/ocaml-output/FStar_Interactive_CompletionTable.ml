open Prims
let (string_compare : Prims.string -> Prims.string -> Prims.int) =
  fun s1 -> fun s2 -> FStar_String.compare s1 s2
type 'a heap =
  | EmptyHeap 
  | Heap of ('a * 'a heap Prims.list) 
let uu___is_EmptyHeap : 'a . 'a heap -> Prims.bool =
  fun projectee ->
    match projectee with | EmptyHeap -> true | uu____69 -> false
let uu___is_Heap : 'a . 'a heap -> Prims.bool =
  fun projectee -> match projectee with | Heap _0 -> true | uu____99 -> false
let __proj__Heap__item___0 : 'a . 'a heap -> ('a * 'a heap Prims.list) =
  fun projectee -> match projectee with | Heap _0 -> _0
let heap_merge :
  'Auu____144 .
    ('Auu____144 -> 'Auu____144 -> Prims.int) ->
      'Auu____144 heap -> 'Auu____144 heap -> 'Auu____144 heap
  =
  fun cmp ->
    fun h1 ->
      fun h2 ->
        match (h1, h2) with
        | (EmptyHeap, h) -> h
        | (h, EmptyHeap) -> h
        | (Heap (v1, hh1), Heap (v2, hh2)) ->
            let uu____224 =
              let uu____226 = cmp v1 v2 in uu____226 < (Prims.parse_int "0") in
            if uu____224
            then Heap (v1, (h2 :: hh1))
            else Heap (v2, (h1 :: hh2))
let heap_insert :
  'Auu____255 .
    ('Auu____255 -> 'Auu____255 -> Prims.int) ->
      'Auu____255 heap -> 'Auu____255 -> 'Auu____255 heap
  = fun cmp -> fun h -> fun v1 -> heap_merge cmp (Heap (v1, [])) h
let rec heap_merge_pairs :
  'Auu____302 .
    ('Auu____302 -> 'Auu____302 -> Prims.int) ->
      'Auu____302 heap Prims.list -> 'Auu____302 heap
  =
  fun cmp ->
    fun uu___0_325 ->
      match uu___0_325 with
      | [] -> EmptyHeap
      | h::[] -> h
      | h1::h2::hh ->
          let uu____359 = heap_merge cmp h1 h2 in
          let uu____362 = heap_merge_pairs cmp hh in
          heap_merge cmp uu____359 uu____362
let heap_peek :
  'Auu____370 .
    'Auu____370 heap -> 'Auu____370 FStar_Pervasives_Native.option
  =
  fun uu___1_379 ->
    match uu___1_379 with
    | EmptyHeap -> FStar_Pervasives_Native.None
    | Heap (v1, uu____383) -> FStar_Pervasives_Native.Some v1
let heap_pop :
  'Auu____399 .
    ('Auu____399 -> 'Auu____399 -> Prims.int) ->
      'Auu____399 heap ->
        ('Auu____399 * 'Auu____399 heap) FStar_Pervasives_Native.option
  =
  fun cmp ->
    fun uu___2_426 ->
      match uu___2_426 with
      | EmptyHeap -> FStar_Pervasives_Native.None
      | Heap (v1, hh) ->
          let uu____450 =
            let uu____457 = heap_merge_pairs cmp hh in (v1, uu____457) in
          FStar_Pervasives_Native.Some uu____450
let heap_from_list :
  'Auu____475 .
    ('Auu____475 -> 'Auu____475 -> Prims.int) ->
      'Auu____475 Prims.list -> 'Auu____475 heap
  =
  fun cmp ->
    fun values -> FStar_List.fold_left (heap_insert cmp) EmptyHeap values
let push_nodup :
  'Auu____515 .
    ('Auu____515 -> Prims.string) ->
      'Auu____515 -> 'Auu____515 Prims.list -> 'Auu____515 Prims.list
  =
  fun key_fn ->
    fun x ->
      fun uu___3_538 ->
        match uu___3_538 with
        | [] -> [x]
        | h::t ->
            let uu____548 =
              let uu____550 =
                let uu____552 = key_fn x in
                let uu____554 = key_fn h in
                string_compare uu____552 uu____554 in
              uu____550 = (Prims.parse_int "0") in
            if uu____548 then h :: t else x :: h :: t
let rec add_priorities :
  'Auu____572 .
    Prims.int ->
      (Prims.int * 'Auu____572) Prims.list ->
        'Auu____572 Prims.list -> (Prims.int * 'Auu____572) Prims.list
  =
  fun n1 ->
    fun acc ->
      fun uu___4_604 ->
        match uu___4_604 with
        | [] -> acc
        | h::t ->
            add_priorities (n1 + (Prims.parse_int "1")) ((n1, h) :: acc) t
let merge_increasing_lists_rev :
  'a . ('a -> Prims.string) -> 'a Prims.list Prims.list -> 'a Prims.list =
  fun key_fn ->
    fun lists ->
      let cmp v1 v2 =
        match (v1, v2) with
        | ((uu____716, []), uu____717) -> failwith "impossible"
        | (uu____745, (uu____746, [])) -> failwith "impossible"
        | ((pr1, h1::uu____776), (pr2, h2::uu____779)) ->
            let cmp_h =
              let uu____808 = key_fn h1 in
              let uu____810 = key_fn h2 in string_compare uu____808 uu____810 in
            if cmp_h <> (Prims.parse_int "0") then cmp_h else pr1 - pr2 in
      let rec aux lists1 acc =
        let uu____853 = heap_pop cmp lists1 in
        match uu____853 with
        | FStar_Pervasives_Native.None -> acc
        | FStar_Pervasives_Native.Some ((pr, []), uu____906) ->
            failwith "impossible"
        | FStar_Pervasives_Native.Some ((pr, v1::[]), lists2) ->
            let uu____1011 = push_nodup key_fn v1 acc in
            aux lists2 uu____1011
        | FStar_Pervasives_Native.Some ((pr, v1::tl1), lists2) ->
            let uu____1069 = heap_insert cmp lists2 (pr, tl1) in
            let uu____1089 = push_nodup key_fn v1 acc in
            aux uu____1069 uu____1089 in
      let lists1 = FStar_List.filter (fun x -> x <> []) lists in
      match lists1 with
      | [] -> []
      | l::[] -> FStar_List.rev l
      | uu____1116 ->
          let lists2 = add_priorities (Prims.parse_int "0") [] lists1 in
          let uu____1141 = heap_from_list cmp lists2 in aux uu____1141 []
type 'a btree =
  | StrEmpty 
  | StrBranch of (Prims.string * 'a * 'a btree * 'a btree) 
let uu___is_StrEmpty : 'a . 'a btree -> Prims.bool =
  fun projectee ->
    match projectee with | StrEmpty -> true | uu____1200 -> false
let uu___is_StrBranch : 'a . 'a btree -> Prims.bool =
  fun projectee ->
    match projectee with | StrBranch _0 -> true | uu____1235 -> false
let __proj__StrBranch__item___0 :
  'a . 'a btree -> (Prims.string * 'a * 'a btree * 'a btree) =
  fun projectee -> match projectee with | StrBranch _0 -> _0
let rec btree_to_list_rev :
  'Auu____1288 .
    'Auu____1288 btree ->
      (Prims.string * 'Auu____1288) Prims.list ->
        (Prims.string * 'Auu____1288) Prims.list
  =
  fun btree ->
    fun acc ->
      match btree with
      | StrEmpty -> acc
      | StrBranch (key, value, lbt, rbt) ->
          let uu____1338 =
            let uu____1346 = btree_to_list_rev lbt acc in (key, value) ::
              uu____1346 in
          btree_to_list_rev rbt uu____1338
let rec btree_from_list :
  'Auu____1367 .
    (Prims.string * 'Auu____1367) Prims.list ->
      Prims.int ->
        ('Auu____1367 btree * (Prims.string * 'Auu____1367) Prims.list)
  =
  fun nodes ->
    fun size ->
      if size = (Prims.parse_int "0")
      then (StrEmpty, nodes)
      else
        (let lbt_size = size / (Prims.parse_int "2") in
         let rbt_size = (size - lbt_size) - (Prims.parse_int "1") in
         let uu____1427 = btree_from_list nodes lbt_size in
         match uu____1427 with
         | (lbt, nodes_left) ->
             (match nodes_left with
              | [] -> failwith "Invalid size passed to btree_from_list"
              | (k, v1)::nodes_left1 ->
                  let uu____1523 = btree_from_list nodes_left1 rbt_size in
                  (match uu____1523 with
                   | (rbt, nodes_left2) ->
                       ((StrBranch (k, v1, lbt, rbt)), nodes_left2))))
let rec btree_insert_replace :
  'a . 'a btree -> Prims.string -> 'a -> 'a btree =
  fun bt ->
    fun k ->
      fun v1 ->
        match bt with
        | StrEmpty -> StrBranch (k, v1, StrEmpty, StrEmpty)
        | StrBranch (k', v', lbt, rbt) ->
            let cmp = string_compare k k' in
            if cmp < (Prims.parse_int "0")
            then
              let uu____1643 =
                let uu____1657 = btree_insert_replace lbt k v1 in
                (k', v', uu____1657, rbt) in
              StrBranch uu____1643
            else
              if cmp > (Prims.parse_int "0")
              then
                (let uu____1671 =
                   let uu____1685 = btree_insert_replace rbt k v1 in
                   (k', v', lbt, uu____1685) in
                 StrBranch uu____1671)
              else StrBranch (k', v1, lbt, rbt)
let rec btree_find_exact :
  'a . 'a btree -> Prims.string -> 'a FStar_Pervasives_Native.option =
  fun bt ->
    fun k ->
      match bt with
      | StrEmpty -> FStar_Pervasives_Native.None
      | StrBranch (k', v1, lbt, rbt) ->
          let cmp = string_compare k k' in
          if cmp < (Prims.parse_int "0")
          then btree_find_exact lbt k
          else
            if cmp > (Prims.parse_int "0")
            then btree_find_exact rbt k
            else FStar_Pervasives_Native.Some v1
let rec btree_extract_min :
  'a .
    'a btree -> (Prims.string * 'a * 'a btree) FStar_Pervasives_Native.option
  =
  fun bt ->
    match bt with
    | StrEmpty -> FStar_Pervasives_Native.None
    | StrBranch (k, v1, StrEmpty, rbt) ->
        FStar_Pervasives_Native.Some (k, v1, rbt)
    | StrBranch (uu____1814, uu____1815, lbt, uu____1817) ->
        btree_extract_min lbt
let rec btree_remove : 'a . 'a btree -> Prims.string -> 'a btree =
  fun bt ->
    fun k ->
      match bt with
      | StrEmpty -> StrEmpty
      | StrBranch (k', v1, lbt, rbt) ->
          let cmp = string_compare k k' in
          if cmp < (Prims.parse_int "0")
          then
            let uu____1875 =
              let uu____1889 = btree_remove lbt k in
              (k', v1, uu____1889, rbt) in
            StrBranch uu____1875
          else
            if cmp > (Prims.parse_int "0")
            then
              (let uu____1903 =
                 let uu____1917 = btree_remove rbt k in
                 (k', v1, lbt, uu____1917) in
               StrBranch uu____1903)
            else
              (match lbt with
               | StrEmpty -> bt
               | uu____1929 ->
                   let uu____1932 = btree_extract_min rbt in
                   (match uu____1932 with
                    | FStar_Pervasives_Native.None -> lbt
                    | FStar_Pervasives_Native.Some
                        (rbt_min_k, rbt_min_v, rbt') ->
                        StrBranch (rbt_min_k, rbt_min_v, lbt, rbt')))
type prefix_match =
  {
  prefix: Prims.string FStar_Pervasives_Native.option ;
  completion: Prims.string }
let (__proj__Mkprefix_match__item__prefix :
  prefix_match -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with | { prefix = prefix1; completion;_} -> prefix1
let (__proj__Mkprefix_match__item__completion : prefix_match -> Prims.string)
  =
  fun projectee ->
    match projectee with | { prefix = prefix1; completion;_} -> completion
type path_elem = {
  imports: Prims.string Prims.list ;
  segment: prefix_match }
let (__proj__Mkpath_elem__item__imports :
  path_elem -> Prims.string Prims.list) =
  fun projectee -> match projectee with | { imports; segment;_} -> imports
let (__proj__Mkpath_elem__item__segment : path_elem -> prefix_match) =
  fun projectee -> match projectee with | { imports; segment;_} -> segment
let (matched_prefix_of_path_elem :
  path_elem -> Prims.string FStar_Pervasives_Native.option) =
  fun elem -> (elem.segment).prefix
let (mk_path_el : Prims.string Prims.list -> prefix_match -> path_elem) =
  fun imports -> fun segment -> { imports; segment }
let rec btree_find_prefix :
  'a . 'a btree -> Prims.string -> (prefix_match * 'a) Prims.list =
  fun bt ->
    fun prefix1 ->
      let rec aux bt1 prefix2 acc =
        match bt1 with
        | StrEmpty -> acc
        | StrBranch (k, v1, lbt, rbt) ->
            let cmp = string_compare k prefix2 in
            let include_middle = FStar_Util.starts_with k prefix2 in
            let explore_right =
              (cmp <= (Prims.parse_int "0")) || include_middle in
            let explore_left = cmp > (Prims.parse_int "0") in
            let matches = if explore_right then aux rbt prefix2 acc else acc in
            let matches1 =
              if include_middle
              then
                ({
                   prefix = (FStar_Pervasives_Native.Some prefix2);
                   completion = k
                 }, v1)
                :: matches
              else matches in
            let matches2 =
              if explore_left then aux lbt prefix2 matches1 else matches1 in
            matches2 in
      aux bt prefix1 []
let rec btree_fold :
  'a 'b . 'a btree -> (Prims.string -> 'a -> 'b -> 'b) -> 'b -> 'b =
  fun bt ->
    fun f ->
      fun acc ->
        match bt with
        | StrEmpty -> acc
        | StrBranch (k, v1, lbt, rbt) ->
            let uu____2313 =
              let uu____2314 = btree_fold rbt f acc in f k v1 uu____2314 in
            btree_fold lbt f uu____2313
type path = path_elem Prims.list
type query = Prims.string Prims.list
let (query_to_string : Prims.string Prims.list -> Prims.string) =
  fun q -> FStar_String.concat "." q
type 'a name_collection =
  | Names of 'a btree 
  | ImportedNames of (Prims.string * 'a name_collection Prims.list) 
let uu___is_Names : 'a . 'a name_collection -> Prims.bool =
  fun projectee ->
    match projectee with | Names _0 -> true | uu____2382 -> false
let __proj__Names__item___0 : 'a . 'a name_collection -> 'a btree =
  fun projectee -> match projectee with | Names _0 -> _0
let uu___is_ImportedNames : 'a . 'a name_collection -> Prims.bool =
  fun projectee ->
    match projectee with | ImportedNames _0 -> true | uu____2433 -> false
let __proj__ImportedNames__item___0 :
  'a . 'a name_collection -> (Prims.string * 'a name_collection Prims.list) =
  fun projectee -> match projectee with | ImportedNames _0 -> _0
type 'a names = 'a name_collection Prims.list
type 'a trie = {
  bindings: 'a names ;
  namespaces: 'a trie names }
let __proj__Mktrie__item__bindings : 'a . 'a trie -> 'a names =
  fun projectee ->
    match projectee with | { bindings; namespaces;_} -> bindings
let __proj__Mktrie__item__namespaces : 'a . 'a trie -> 'a trie names =
  fun projectee ->
    match projectee with | { bindings; namespaces;_} -> namespaces
let trie_empty : 'Auu____2554 . unit -> 'Auu____2554 trie =
  fun uu____2557 -> { bindings = []; namespaces = [] }
let rec names_find_exact :
  'a . 'a names -> Prims.string -> 'a FStar_Pervasives_Native.option =
  fun names ->
    fun ns ->
      let uu____2591 =
        match names with
        | [] -> (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (Names bt)::names1 ->
            let uu____2632 = btree_find_exact bt ns in
            (uu____2632, (FStar_Pervasives_Native.Some names1))
        | (ImportedNames (uu____2643, names1))::more_names ->
            let uu____2662 = names_find_exact names1 ns in
            (uu____2662, (FStar_Pervasives_Native.Some more_names)) in
      match uu____2591 with
      | (result, names1) ->
          (match (result, names1) with
           | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some
              scopes) -> names_find_exact scopes ns
           | uu____2708 -> result)
let rec trie_descend_exact :
  'a . 'a trie -> query -> 'a trie FStar_Pervasives_Native.option =
  fun tr ->
    fun query ->
      match query with
      | [] -> FStar_Pervasives_Native.Some tr
      | ns::query1 ->
          let uu____2756 = names_find_exact tr.namespaces ns in
          FStar_Util.bind_opt uu____2756
            (fun scope -> trie_descend_exact scope query1)
let rec trie_find_exact :
  'a . 'a trie -> query -> 'a FStar_Pervasives_Native.option =
  fun tr ->
    fun query ->
      match query with
      | [] -> failwith "Empty query in trie_find_exact"
      | name::[] -> names_find_exact tr.bindings name
      | ns::query1 ->
          let uu____2811 = names_find_exact tr.namespaces ns in
          FStar_Util.bind_opt uu____2811
            (fun scope -> trie_find_exact scope query1)
let names_insert : 'a . 'a names -> Prims.string -> 'a -> 'a names =
  fun name_collections ->
    fun id1 ->
      fun v1 ->
        let uu____2857 =
          match name_collections with
          | (Names bt)::tl1 -> (bt, tl1)
          | uu____2894 -> (StrEmpty, name_collections) in
        match uu____2857 with
        | (bt, name_collections1) ->
            let uu____2919 =
              let uu____2922 = btree_insert_replace bt id1 v1 in
              Names uu____2922 in
            uu____2919 :: name_collections1
let rec namespaces_mutate :
  'a .
    'a trie names ->
      Prims.string ->
        query ->
          query ->
            ('a trie ->
               Prims.string -> query -> query -> 'a trie names -> 'a trie)
              -> ('a trie -> query -> 'a trie) -> 'a trie names
  =
  fun namespaces ->
    fun ns ->
      fun q ->
        fun rev_acc1 ->
          fun mut_node ->
            fun mut_leaf ->
              let trie =
                let uu____3122 = names_find_exact namespaces ns in
                FStar_Util.dflt (trie_empty ()) uu____3122 in
              let uu____3131 = trie_mutate trie q rev_acc1 mut_node mut_leaf in
              names_insert namespaces ns uu____3131
and trie_mutate :
  'a .
    'a trie ->
      query ->
        query ->
          ('a trie ->
             Prims.string -> query -> query -> 'a trie names -> 'a trie)
            -> ('a trie -> query -> 'a trie) -> 'a trie
  =
  fun tr ->
    fun q ->
      fun rev_acc1 ->
        fun mut_node ->
          fun mut_leaf ->
            match q with
            | [] -> mut_leaf tr rev_acc1
            | id1::q1 ->
                let ns' =
                  namespaces_mutate tr.namespaces id1 q1 (id1 :: rev_acc1)
                    mut_node mut_leaf in
                mut_node tr id1 q1 rev_acc1 ns'
let trie_mutate_leaf :
  'a . 'a trie -> query -> ('a trie -> query -> 'a trie) -> 'a trie =
  fun tr ->
    fun query ->
      trie_mutate tr query []
        (fun tr1 ->
           fun uu____3231 ->
             fun uu____3232 ->
               fun uu____3233 ->
                 fun namespaces ->
                   let uu___379_3242 = tr1 in
                   { bindings = (uu___379_3242.bindings); namespaces })
let trie_insert : 'a . 'a trie -> query -> Prims.string -> 'a -> 'a trie =
  fun tr ->
    fun ns_query ->
      fun id1 ->
        fun v1 ->
          trie_mutate_leaf tr ns_query
            (fun tr1 ->
               fun uu____3290 ->
                 let uu___388_3293 = tr1 in
                 let uu____3296 = names_insert tr1.bindings id1 v1 in
                 {
                   bindings = uu____3296;
                   namespaces = (uu___388_3293.namespaces)
                 })
let trie_import :
  'a .
    'a trie ->
      query ->
        query -> ('a trie -> 'a trie -> Prims.string -> 'a trie) -> 'a trie
  =
  fun tr ->
    fun host_query ->
      fun included_query ->
        fun mutator ->
          let label = query_to_string included_query in
          let included_trie =
            let uu____3371 = trie_descend_exact tr included_query in
            FStar_Util.dflt (trie_empty ()) uu____3371 in
          trie_mutate_leaf tr host_query
            (fun tr1 -> fun uu____3381 -> mutator tr1 included_trie label)
let trie_include : 'a . 'a trie -> query -> query -> 'a trie =
  fun tr ->
    fun host_query ->
      fun included_query ->
        trie_import tr host_query included_query
          (fun tr1 ->
             fun inc ->
               fun label ->
                 let uu___406_3427 = tr1 in
                 {
                   bindings = ((ImportedNames (label, (inc.bindings))) ::
                     (tr1.bindings));
                   namespaces = (uu___406_3427.namespaces)
                 })
let trie_open_namespace : 'a . 'a trie -> query -> query -> 'a trie =
  fun tr ->
    fun host_query ->
      fun included_query ->
        trie_import tr host_query included_query
          (fun tr1 ->
             fun inc ->
               fun label ->
                 let uu___415_3480 = tr1 in
                 {
                   bindings = (uu___415_3480.bindings);
                   namespaces = ((ImportedNames (label, (inc.namespaces))) ::
                     (tr1.namespaces))
                 })
let trie_add_alias :
  'a . 'a trie -> Prims.string -> query -> query -> 'a trie =
  fun tr ->
    fun key ->
      fun host_query ->
        fun included_query ->
          trie_import tr host_query included_query
            (fun tr1 ->
               fun inc ->
                 fun label ->
                   trie_mutate_leaf tr1 [key]
                     (fun _ignored_overwritten_trie ->
                        fun uu____3552 ->
                          {
                            bindings =
                              [ImportedNames (label, (inc.bindings))];
                            namespaces = []
                          }))
let names_revmap :
  'a 'b .
    ('a btree -> 'b) -> 'a names -> (Prims.string Prims.list * 'b) Prims.list
  =
  fun fn ->
    fun name_collections ->
      let rec aux acc imports name_collections1 =
        FStar_List.fold_left
          (fun acc1 ->
             fun uu___5_3689 ->
               match uu___5_3689 with
               | Names bt ->
                   let uu____3713 =
                     let uu____3721 = fn bt in (imports, uu____3721) in
                   uu____3713 :: acc1
               | ImportedNames (nm, name_collections2) ->
                   aux acc1 (nm :: imports) name_collections2) acc
          name_collections1 in
      aux [] [] name_collections
let btree_find_all :
  'a .
    Prims.string FStar_Pervasives_Native.option ->
      'a btree -> (prefix_match * 'a) Prims.list
  =
  fun prefix1 ->
    fun bt ->
      btree_fold bt
        (fun k ->
           fun tr ->
             fun acc -> ({ prefix = prefix1; completion = k }, tr) :: acc) []
type name_search_term =
  | NSTAll 
  | NSTNone 
  | NSTPrefix of Prims.string 
let (uu___is_NSTAll : name_search_term -> Prims.bool) =
  fun projectee ->
    match projectee with | NSTAll -> true | uu____3829 -> false
let (uu___is_NSTNone : name_search_term -> Prims.bool) =
  fun projectee ->
    match projectee with | NSTNone -> true | uu____3840 -> false
let (uu___is_NSTPrefix : name_search_term -> Prims.bool) =
  fun projectee ->
    match projectee with | NSTPrefix _0 -> true | uu____3853 -> false
let (__proj__NSTPrefix__item___0 : name_search_term -> Prims.string) =
  fun projectee -> match projectee with | NSTPrefix _0 -> _0
let names_find_rev :
  'a . 'a names -> name_search_term -> (path_elem * 'a) Prims.list =
  fun names ->
    fun id1 ->
      let matching_values_per_collection_with_imports =
        match id1 with
        | NSTNone -> []
        | NSTAll ->
            names_revmap (btree_find_all FStar_Pervasives_Native.None) names
        | NSTPrefix "" ->
            names_revmap (btree_find_all (FStar_Pervasives_Native.Some ""))
              names
        | NSTPrefix id2 ->
            names_revmap (fun bt -> btree_find_prefix bt id2) names in
      let matching_values_per_collection =
        FStar_List.map
          (fun uu____3996 ->
             match uu____3996 with
             | (imports, matches) ->
                 FStar_List.map
                   (fun uu____4047 ->
                      match uu____4047 with
                      | (segment, v1) -> ((mk_path_el imports segment), v1))
                   matches) matching_values_per_collection_with_imports in
      merge_increasing_lists_rev
        (fun uu____4065 ->
           match uu____4065 with
           | (path_el, uu____4072) -> (path_el.segment).completion)
        matching_values_per_collection
let rec trie_find_prefix' :
  'a .
    'a trie ->
      path -> query -> (path * 'a) Prims.list -> (path * 'a) Prims.list
  =
  fun tr ->
    fun path_acc ->
      fun query ->
        fun acc ->
          let uu____4127 =
            match query with
            | [] -> (NSTAll, NSTAll, [])
            | id1::[] -> ((NSTPrefix id1), (NSTPrefix id1), [])
            | ns::query1 -> ((NSTPrefix ns), NSTNone, query1) in
          match uu____4127 with
          | (ns_search_term, bindings_search_term, query1) ->
              let matching_namespaces_rev =
                names_find_rev tr.namespaces ns_search_term in
              let acc_with_recursive_bindings =
                FStar_List.fold_left
                  (fun acc1 ->
                     fun uu____4198 ->
                       match uu____4198 with
                       | (path_el, trie) ->
                           trie_find_prefix' trie (path_el :: path_acc)
                             query1 acc1) acc matching_namespaces_rev in
              let matching_bindings_rev =
                names_find_rev tr.bindings bindings_search_term in
              FStar_List.rev_map_onto
                (fun uu____4243 ->
                   match uu____4243 with
                   | (path_el, v1) ->
                       ((FStar_List.rev (path_el :: path_acc)), v1))
                matching_bindings_rev acc_with_recursive_bindings
let trie_find_prefix : 'a . 'a trie -> query -> (path * 'a) Prims.list =
  fun tr -> fun query -> trie_find_prefix' tr [] query []
type ns_info = {
  ns_name: Prims.string ;
  ns_loaded: Prims.bool }
let (__proj__Mkns_info__item__ns_name : ns_info -> Prims.string) =
  fun projectee -> match projectee with | { ns_name; ns_loaded;_} -> ns_name
let (__proj__Mkns_info__item__ns_loaded : ns_info -> Prims.bool) =
  fun projectee ->
    match projectee with | { ns_name; ns_loaded;_} -> ns_loaded
type mod_info =
  {
  mod_name: Prims.string ;
  mod_path: Prims.string ;
  mod_loaded: Prims.bool }
let (__proj__Mkmod_info__item__mod_name : mod_info -> Prims.string) =
  fun projectee ->
    match projectee with | { mod_name; mod_path; mod_loaded;_} -> mod_name
let (__proj__Mkmod_info__item__mod_path : mod_info -> Prims.string) =
  fun projectee ->
    match projectee with | { mod_name; mod_path; mod_loaded;_} -> mod_path
let (__proj__Mkmod_info__item__mod_loaded : mod_info -> Prims.bool) =
  fun projectee ->
    match projectee with | { mod_name; mod_path; mod_loaded;_} -> mod_loaded
let (mod_name : mod_info -> Prims.string) = fun md -> md.mod_name
type mod_symbol =
  | Module of mod_info 
  | Namespace of ns_info 
let (uu___is_Module : mod_symbol -> Prims.bool) =
  fun projectee ->
    match projectee with | Module _0 -> true | uu____4413 -> false
let (__proj__Module__item___0 : mod_symbol -> mod_info) =
  fun projectee -> match projectee with | Module _0 -> _0
let (uu___is_Namespace : mod_symbol -> Prims.bool) =
  fun projectee ->
    match projectee with | Namespace _0 -> true | uu____4432 -> false
let (__proj__Namespace__item___0 : mod_symbol -> ns_info) =
  fun projectee -> match projectee with | Namespace _0 -> _0
type lid_symbol = FStar_Ident.lid
type symbol =
  | ModOrNs of mod_symbol 
  | Lid of lid_symbol 
let (uu___is_ModOrNs : symbol -> Prims.bool) =
  fun projectee ->
    match projectee with | ModOrNs _0 -> true | uu____4461 -> false
let (__proj__ModOrNs__item___0 : symbol -> mod_symbol) =
  fun projectee -> match projectee with | ModOrNs _0 -> _0
let (uu___is_Lid : symbol -> Prims.bool) =
  fun projectee ->
    match projectee with | Lid _0 -> true | uu____4480 -> false
let (__proj__Lid__item___0 : symbol -> lid_symbol) =
  fun projectee -> match projectee with | Lid _0 -> _0
type table = {
  tbl_lids: lid_symbol trie ;
  tbl_mods: mod_symbol trie }
let (__proj__Mktable__item__tbl_lids : table -> lid_symbol trie) =
  fun projectee -> match projectee with | { tbl_lids; tbl_mods;_} -> tbl_lids
let (__proj__Mktable__item__tbl_mods : table -> mod_symbol trie) =
  fun projectee -> match projectee with | { tbl_lids; tbl_mods;_} -> tbl_mods
let (empty : table) =
  { tbl_lids = (trie_empty ()); tbl_mods = (trie_empty ()) }
let (insert : table -> query -> Prims.string -> lid_symbol -> table) =
  fun tbl ->
    fun host_query ->
      fun id1 ->
        fun c ->
          let uu___533_4559 = tbl in
          let uu____4560 = trie_insert tbl.tbl_lids host_query id1 c in
          { tbl_lids = uu____4560; tbl_mods = (uu___533_4559.tbl_mods) }
let (register_alias : table -> Prims.string -> query -> query -> table) =
  fun tbl ->
    fun key ->
      fun host_query ->
        fun included_query ->
          let uu___543_4586 = tbl in
          let uu____4587 =
            trie_add_alias tbl.tbl_lids key host_query included_query in
          { tbl_lids = uu____4587; tbl_mods = (uu___543_4586.tbl_mods) }
let (register_include : table -> query -> query -> table) =
  fun tbl ->
    fun host_query ->
      fun included_query ->
        let uu___551_4606 = tbl in
        let uu____4607 = trie_include tbl.tbl_lids host_query included_query in
        { tbl_lids = uu____4607; tbl_mods = (uu___551_4606.tbl_mods) }
let (register_open : table -> Prims.bool -> query -> query -> table) =
  fun tbl ->
    fun is_module ->
      fun host_query ->
        fun included_query ->
          if is_module
          then register_include tbl host_query included_query
          else
            (let uu___562_4636 = tbl in
             let uu____4637 =
               trie_open_namespace tbl.tbl_lids host_query included_query in
             { tbl_lids = uu____4637; tbl_mods = (uu___562_4636.tbl_mods) })
let (register_module_path :
  table -> Prims.bool -> Prims.string -> query -> table) =
  fun tbl ->
    fun loaded ->
      fun path ->
        fun mod_query ->
          let ins_ns id1 bindings full_name loaded1 =
            let uu____4698 =
              let uu____4706 = names_find_exact bindings id1 in
              (uu____4706, loaded1) in
            match uu____4698 with
            | (FStar_Pervasives_Native.None, uu____4714) ->
                names_insert bindings id1
                  (Namespace { ns_name = full_name; ns_loaded = loaded1 })
            | (FStar_Pervasives_Native.Some (Namespace
               { ns_name = uu____4719; ns_loaded = false;_}), true) ->
                names_insert bindings id1
                  (Namespace { ns_name = full_name; ns_loaded = loaded1 })
            | (FStar_Pervasives_Native.Some uu____4726, uu____4727) ->
                bindings in
          let ins_mod id1 bindings full_name loaded1 =
            names_insert bindings id1
              (Module
                 {
                   mod_name = full_name;
                   mod_path = path;
                   mod_loaded = loaded1
                 }) in
          let name_of_revq query =
            FStar_String.concat "." (FStar_List.rev query) in
          let ins id1 q revq bindings loaded1 =
            let name = name_of_revq (id1 :: revq) in
            match q with
            | [] -> ins_mod id1 bindings name loaded1
            | uu____4834 -> ins_ns id1 bindings name loaded1 in
          let uu___607_4838 = tbl in
          let uu____4839 =
            trie_mutate tbl.tbl_mods mod_query []
              (fun tr ->
                 fun id1 ->
                   fun q ->
                     fun revq ->
                       fun namespaces ->
                         let uu___616_4862 = tr in
                         let uu____4865 = ins id1 q revq tr.bindings loaded in
                         { bindings = uu____4865; namespaces })
              (fun tr -> fun uu____4871 -> tr) in
          { tbl_lids = (uu___607_4838.tbl_lids); tbl_mods = uu____4839 }
let (string_of_path : path -> Prims.string) =
  fun path ->
    let uu____4882 = FStar_List.map (fun el -> (el.segment).completion) path in
    FStar_String.concat "." uu____4882
let (match_length_of_path : path -> Prims.int) =
  fun path ->
    let uu____4898 =
      FStar_List.fold_left
        (fun acc ->
           fun elem ->
             let uu____4938 = acc in
             match uu____4938 with
             | (acc_len, uu____4960) ->
                 (match (elem.segment).prefix with
                  | FStar_Pervasives_Native.Some prefix1 ->
                      let completion_len =
                        FStar_String.length (elem.segment).completion in
                      (((acc_len + (Prims.parse_int "1")) + completion_len),
                        (prefix1, completion_len))
                  | FStar_Pervasives_Native.None -> acc))
        ((Prims.parse_int "0"), ("", (Prims.parse_int "0"))) path in
    match uu____4898 with
    | (length1, (last_prefix, last_completion_length)) ->
        ((length1 - (Prims.parse_int "1")) - last_completion_length) +
          (FStar_String.length last_prefix)
let (first_import_of_path :
  path -> Prims.string FStar_Pervasives_Native.option) =
  fun path ->
    match path with
    | [] -> FStar_Pervasives_Native.None
    | { imports; segment = uu____5034;_}::uu____5035 ->
        FStar_List.last imports
let (alist_of_ns_info :
  ns_info -> (Prims.string * FStar_Util.json) Prims.list) =
  fun ns_info ->
    [("name", (FStar_Util.JsonStr (ns_info.ns_name)));
    ("loaded", (FStar_Util.JsonBool (ns_info.ns_loaded)))]
let (alist_of_mod_info :
  mod_info -> (Prims.string * FStar_Util.json) Prims.list) =
  fun mod_info ->
    [("name", (FStar_Util.JsonStr (mod_info.mod_name)));
    ("path", (FStar_Util.JsonStr (mod_info.mod_path)));
    ("loaded", (FStar_Util.JsonBool (mod_info.mod_loaded)))]
type completion_result =
  {
  completion_match_length: Prims.int ;
  completion_candidate: Prims.string ;
  completion_annotation: Prims.string }
let (__proj__Mkcompletion_result__item__completion_match_length :
  completion_result -> Prims.int) =
  fun projectee ->
    match projectee with
    | { completion_match_length; completion_candidate;
        completion_annotation;_} -> completion_match_length
let (__proj__Mkcompletion_result__item__completion_candidate :
  completion_result -> Prims.string) =
  fun projectee ->
    match projectee with
    | { completion_match_length; completion_candidate;
        completion_annotation;_} -> completion_candidate
let (__proj__Mkcompletion_result__item__completion_annotation :
  completion_result -> Prims.string) =
  fun projectee ->
    match projectee with
    | { completion_match_length; completion_candidate;
        completion_annotation;_} -> completion_annotation
let (json_of_completion_result : completion_result -> FStar_Util.json) =
  fun result ->
    FStar_Util.JsonList
      [FStar_Util.JsonInt (result.completion_match_length);
      FStar_Util.JsonStr (result.completion_annotation);
      FStar_Util.JsonStr (result.completion_candidate)]
let completion_result_of_lid :
  'Auu____5184 . (path * 'Auu____5184) -> completion_result =
  fun uu____5193 ->
    match uu____5193 with
    | (path, _lid) ->
        let uu____5200 = match_length_of_path path in
        let uu____5202 = string_of_path path in
        let uu____5204 =
          let uu____5206 = first_import_of_path path in
          FStar_Util.dflt "" uu____5206 in
        {
          completion_match_length = uu____5200;
          completion_candidate = uu____5202;
          completion_annotation = uu____5204
        }
let (completion_result_of_mod :
  Prims.string -> Prims.bool -> path -> completion_result) =
  fun annot ->
    fun loaded ->
      fun path ->
        let uu____5232 = match_length_of_path path in
        let uu____5234 = string_of_path path in
        let uu____5236 =
          FStar_Util.format1 (if loaded then " %s " else "(%s)") annot in
        {
          completion_match_length = uu____5232;
          completion_candidate = uu____5234;
          completion_annotation = uu____5236
        }
let (completion_result_of_ns_or_mod :
  (path * mod_symbol) -> completion_result) =
  fun uu____5253 ->
    match uu____5253 with
    | (path, symb) ->
        (match symb with
         | Module
             { mod_name = uu____5260; mod_path = uu____5261;
               mod_loaded = loaded;_}
             -> completion_result_of_mod "mod" loaded path
         | Namespace { ns_name = uu____5267; ns_loaded = loaded;_} ->
             completion_result_of_mod "ns" loaded path)
let (find_module_or_ns :
  table -> query -> mod_symbol FStar_Pervasives_Native.option) =
  fun tbl -> fun query -> trie_find_exact tbl.tbl_mods query
let (autocomplete_lid : table -> query -> completion_result Prims.list) =
  fun tbl ->
    fun query ->
      let uu____5298 = trie_find_prefix tbl.tbl_lids query in
      FStar_List.map completion_result_of_lid uu____5298
let (autocomplete_mod_or_ns :
  table ->
    query ->
      ((path * mod_symbol) ->
         (path * mod_symbol) FStar_Pervasives_Native.option)
        -> completion_result Prims.list)
  =
  fun tbl ->
    fun query ->
      fun filter1 ->
        let uu____5352 =
          let uu____5359 = trie_find_prefix tbl.tbl_mods query in
          FStar_All.pipe_right uu____5359 (FStar_List.filter_map filter1) in
        FStar_All.pipe_right uu____5352
          (FStar_List.map completion_result_of_ns_or_mod)