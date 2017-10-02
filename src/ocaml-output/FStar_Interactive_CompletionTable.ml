open Prims
let string_compare: Prims.string -> Prims.string -> Prims.int =
  fun s1  -> fun s2  -> FStar_String.compare s1 s2
type 'a heap =
  | EmptyHeap
  | Heap of ('a,'a heap Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                    show]
let uu___is_EmptyHeap: 'a . 'a heap -> Prims.bool =
  fun projectee  ->
    match projectee with | EmptyHeap  -> true | uu____41 -> false
let uu___is_Heap: 'a . 'a heap -> Prims.bool =
  fun projectee  ->
    match projectee with | Heap _0 -> true | uu____66 -> false
let __proj__Heap__item___0:
  'a . 'a heap -> ('a,'a heap Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Heap _0 -> _0
let heap_merge:
  'Auu____110 .
    ('Auu____110 -> 'Auu____110 -> Prims.int) ->
      'Auu____110 heap -> 'Auu____110 heap -> 'Auu____110 heap
  =
  fun cmp  ->
    fun h1  ->
      fun h2  ->
        match (h1, h2) with
        | (EmptyHeap ,h) -> h
        | (h,EmptyHeap ) -> h
        | (Heap (v1,hh1),Heap (v2,hh2)) ->
            let uu____185 =
              let uu____186 = cmp v1 v2 in uu____186 < (Prims.parse_int "0") in
            if uu____185
            then Heap (v1, (h2 :: hh1))
            else Heap (v2, (h1 :: hh2))
let heap_insert:
  'Auu____210 .
    ('Auu____210 -> 'Auu____210 -> Prims.int) ->
      'Auu____210 heap -> 'Auu____210 -> 'Auu____210 heap
  = fun cmp  -> fun h  -> fun v1  -> heap_merge cmp (Heap (v1, [])) h
let rec heap_merge_pairs:
  'Auu____251 .
    ('Auu____251 -> 'Auu____251 -> Prims.int) ->
      'Auu____251 heap Prims.list -> 'Auu____251 heap
  =
  fun cmp  ->
    fun uu___162_271  ->
      match uu___162_271 with
      | [] -> EmptyHeap
      | h::[] -> h
      | h1::h2::hh ->
          let uu____304 = heap_merge cmp h1 h2 in
          let uu____307 = heap_merge_pairs cmp hh in
          heap_merge cmp uu____304 uu____307
let heap_peek:
  'Auu____314 .
    'Auu____314 heap -> 'Auu____314 FStar_Pervasives_Native.option
  =
  fun uu___163_322  ->
    match uu___163_322 with
    | EmptyHeap  -> FStar_Pervasives_Native.None
    | Heap (v1,uu____326) -> FStar_Pervasives_Native.Some v1
let heap_pop:
  'Auu____341 .
    ('Auu____341 -> 'Auu____341 -> Prims.int) ->
      'Auu____341 heap ->
        ('Auu____341,'Auu____341 heap) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option
  =
  fun cmp  ->
    fun uu___164_365  ->
      match uu___164_365 with
      | EmptyHeap  -> FStar_Pervasives_Native.None
      | Heap (v1,hh) ->
          let uu____388 =
            let uu____395 = heap_merge_pairs cmp hh in (v1, uu____395) in
          FStar_Pervasives_Native.Some uu____388
let heap_from_list:
  'Auu____412 .
    ('Auu____412 -> 'Auu____412 -> Prims.int) ->
      'Auu____412 Prims.list -> 'Auu____412 heap
  =
  fun cmp  ->
    fun values  -> FStar_List.fold_left (heap_insert cmp) EmptyHeap values
let push_nodup:
  'Auu____447 .
    ('Auu____447 -> Prims.string) ->
      'Auu____447 -> 'Auu____447 Prims.list -> 'Auu____447 Prims.list
  =
  fun key_fn  ->
    fun x  ->
      fun uu___165_466  ->
        match uu___165_466 with
        | [] -> [x]
        | h::t ->
            let uu____475 =
              let uu____476 =
                let uu____477 = key_fn x in
                let uu____478 = key_fn h in
                string_compare uu____477 uu____478 in
              uu____476 = (Prims.parse_int "0") in
            if uu____475 then h :: t else x :: h :: t
let rec add_priorities:
  'Auu____490 .
    Prims.int ->
      (Prims.int,'Auu____490) FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____490 Prims.list ->
          (Prims.int,'Auu____490) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun n1  ->
    fun acc  ->
      fun uu___166_516  ->
        match uu___166_516 with
        | [] -> acc
        | h::t ->
            add_priorities (n1 + (Prims.parse_int "1")) ((n1, h) :: acc) t
let merge_increasing_lists_rev:
  'a . ('a -> Prims.string) -> 'a Prims.list Prims.list -> 'a Prims.list =
  fun key_fn  ->
    fun lists  ->
      let cmp v1 v2 =
        match (v1, v2) with
        | ((uu____606,[]),uu____607) -> failwith "impossible"
        | (uu____628,(uu____629,[])) -> failwith "impossible"
        | ((pr1,h1::uu____652),(pr2,h2::uu____655)) ->
            let cmp_h =
              let uu____677 = key_fn h1 in
              let uu____678 = key_fn h2 in string_compare uu____677 uu____678 in
            if cmp_h <> (Prims.parse_int "0") then cmp_h else pr1 - pr2 in
      let rec aux lists1 acc =
        let uu____709 = heap_pop cmp lists1 in
        match uu____709 with
        | FStar_Pervasives_Native.None  -> acc
        | FStar_Pervasives_Native.Some ((pr,[]),uu____757) ->
            failwith "impossible"
        | FStar_Pervasives_Native.Some ((pr,v1::[]),lists2) ->
            let uu____847 = push_nodup key_fn v1 acc in aux lists2 uu____847
        | FStar_Pervasives_Native.Some ((pr,v1::tl1),lists2) ->
            let uu____898 = heap_insert cmp lists2 (pr, tl1) in
            let uu____915 = push_nodup key_fn v1 acc in
            aux uu____898 uu____915 in
      let lists1 = FStar_List.filter (fun x  -> x <> []) lists in
      match lists1 with
      | [] -> []
      | l::[] -> FStar_List.rev l
      | uu____942 ->
          let lists2 = add_priorities (Prims.parse_int "0") [] lists1 in
          let uu____964 = heap_from_list cmp lists2 in aux uu____964 []
type 'a btree =
  | StrEmpty
  | StrBranch of (Prims.string,'a,'a btree,'a btree)
  FStar_Pervasives_Native.tuple4[@@deriving show]
let uu___is_StrEmpty: 'a . 'a btree -> Prims.bool =
  fun projectee  ->
    match projectee with | StrEmpty  -> true | uu____1015 -> false
let uu___is_StrBranch: 'a . 'a btree -> Prims.bool =
  fun projectee  ->
    match projectee with | StrBranch _0 -> true | uu____1044 -> false
let __proj__StrBranch__item___0:
  'a .
    'a btree ->
      (Prims.string,'a,'a btree,'a btree) FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | StrBranch _0 -> _0
let rec btree_to_list_rev:
  'Auu____1094 .
    'Auu____1094 btree ->
      (Prims.string,'Auu____1094) FStar_Pervasives_Native.tuple2 Prims.list
        ->
        (Prims.string,'Auu____1094) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun btree  ->
    fun acc  ->
      match btree with
      | StrEmpty  -> acc
      | StrBranch (key,value,lbt,rbt) ->
          let uu____1137 =
            let uu____1144 = btree_to_list_rev lbt acc in (key, value) ::
              uu____1144 in
          btree_to_list_rev rbt uu____1137
let rec btree_from_list:
  'Auu____1161 .
    (Prims.string,'Auu____1161) FStar_Pervasives_Native.tuple2 Prims.list ->
      Prims.int ->
        ('Auu____1161 btree,(Prims.string,'Auu____1161)
                              FStar_Pervasives_Native.tuple2 Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun nodes  ->
    fun size  ->
      if size = (Prims.parse_int "0")
      then (StrEmpty, nodes)
      else
        (let lbt_size = size / (Prims.parse_int "2") in
         let rbt_size = (size - lbt_size) - (Prims.parse_int "1") in
         let uu____1205 = btree_from_list nodes lbt_size in
         match uu____1205 with
         | (lbt,nodes_left) ->
             (match nodes_left with
              | [] -> failwith "Invalid size passed to btree_from_list"
              | (k,v1)::nodes_left1 ->
                  let uu____1289 = btree_from_list nodes_left1 rbt_size in
                  (match uu____1289 with
                   | (rbt,nodes_left2) ->
                       ((StrBranch (k, v1, lbt, rbt)), nodes_left2))))
let rec btree_insert_replace: 'a . 'a btree -> Prims.string -> 'a -> 'a btree
  =
  fun bt  ->
    fun k  ->
      fun v1  ->
        match bt with
        | StrEmpty  -> StrBranch (k, v1, StrEmpty, StrEmpty)
        | StrBranch (k',v',lbt,rbt) ->
            let cmp = string_compare k k' in
            if cmp < (Prims.parse_int "0")
            then
              let uu____1390 =
                let uu____1403 = btree_insert_replace lbt k v1 in
                (k', v', uu____1403, rbt) in
              StrBranch uu____1390
            else
              if cmp > (Prims.parse_int "0")
              then
                (let uu____1413 =
                   let uu____1426 = btree_insert_replace rbt k v1 in
                   (k', v', lbt, uu____1426) in
                 StrBranch uu____1413)
              else StrBranch (k', v1, lbt, rbt)
let rec btree_find_exact:
  'a . 'a btree -> Prims.string -> 'a FStar_Pervasives_Native.option =
  fun bt  ->
    fun k  ->
      match bt with
      | StrEmpty  -> FStar_Pervasives_Native.None
      | StrBranch (k',v1,lbt,rbt) ->
          let cmp = string_compare k k' in
          if cmp < (Prims.parse_int "0")
          then btree_find_exact lbt k
          else
            if cmp > (Prims.parse_int "0")
            then btree_find_exact rbt k
            else FStar_Pervasives_Native.Some v1
let rec btree_extract_min:
  'a .
    'a btree ->
      (Prims.string,'a,'a btree) FStar_Pervasives_Native.tuple3
        FStar_Pervasives_Native.option
  =
  fun bt  ->
    match bt with
    | StrEmpty  -> FStar_Pervasives_Native.None
    | StrBranch (k,v1,StrEmpty ,rbt) ->
        FStar_Pervasives_Native.Some (k, v1, rbt)
    | StrBranch (uu____1528,uu____1529,lbt,uu____1531) ->
        btree_extract_min lbt
let rec btree_remove: 'a . 'a btree -> Prims.string -> 'a btree =
  fun bt  ->
    fun k  ->
      match bt with
      | StrEmpty  -> StrEmpty
      | StrBranch (k',v1,lbt,rbt) ->
          let cmp = string_compare k k' in
          if cmp < (Prims.parse_int "0")
          then
            let uu____1576 =
              let uu____1589 = btree_remove lbt k in
              (k', v1, uu____1589, rbt) in
            StrBranch uu____1576
          else
            if cmp > (Prims.parse_int "0")
            then
              (let uu____1599 =
                 let uu____1612 = btree_remove rbt k in
                 (k', v1, lbt, uu____1612) in
               StrBranch uu____1599)
            else
              (match lbt with
               | StrEmpty  -> bt
               | uu____1622 ->
                   let uu____1625 = btree_extract_min rbt in
                   (match uu____1625 with
                    | FStar_Pervasives_Native.None  -> lbt
                    | FStar_Pervasives_Native.Some (rbt_min_k,rbt_min_v,rbt')
                        -> StrBranch (rbt_min_k, rbt_min_v, lbt, rbt')))
type prefix_match =
  {
  prefix: Prims.string FStar_Pervasives_Native.option;
  completion: Prims.string;}[@@deriving show]
let __proj__Mkprefix_match__item__prefix:
  prefix_match -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { prefix = __fname__prefix; completion = __fname__completion;_} ->
        __fname__prefix
let __proj__Mkprefix_match__item__completion: prefix_match -> Prims.string =
  fun projectee  ->
    match projectee with
    | { prefix = __fname__prefix; completion = __fname__completion;_} ->
        __fname__completion
type path_elem = {
  imports: Prims.string Prims.list;
  segment: prefix_match;}[@@deriving show]
let __proj__Mkpath_elem__item__imports: path_elem -> Prims.string Prims.list
  =
  fun projectee  ->
    match projectee with
    | { imports = __fname__imports; segment = __fname__segment;_} ->
        __fname__imports
let __proj__Mkpath_elem__item__segment: path_elem -> prefix_match =
  fun projectee  ->
    match projectee with
    | { imports = __fname__imports; segment = __fname__segment;_} ->
        __fname__segment
let matched_prefix_of_path_elem:
  path_elem -> Prims.string FStar_Pervasives_Native.option =
  fun elem  -> (elem.segment).prefix
let mk_path_el: Prims.string Prims.list -> prefix_match -> path_elem =
  fun imports  -> fun segment  -> { imports; segment }
let rec btree_find_prefix:
  'a .
    'a btree ->
      Prims.string ->
        (prefix_match,'a) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun bt  ->
    fun prefix1  ->
      let rec aux bt1 prefix2 acc =
        match bt1 with
        | StrEmpty  -> acc
        | StrBranch (k,v1,lbt,rbt) ->
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
let rec btree_fold:
  'a 'b . 'a btree -> (Prims.string -> 'a -> 'b -> 'b) -> 'b -> 'b =
  fun bt  ->
    fun f  ->
      fun acc  ->
        match bt with
        | StrEmpty  -> acc
        | StrBranch (k,v1,lbt,rbt) ->
            let uu____1927 =
              let uu____1928 = btree_fold rbt f acc in f k v1 uu____1928 in
            btree_fold lbt f uu____1927
type path = path_elem Prims.list[@@deriving show]
type query = Prims.string Prims.list[@@deriving show]
let query_to_string: Prims.string Prims.list -> Prims.string =
  fun q  -> FStar_String.concat "." q
type 'a name_collection =
  | Names of 'a btree
  | ImportedNames of (Prims.string,'a name_collection Prims.list)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_Names: 'a . 'a name_collection -> Prims.bool =
  fun projectee  ->
    match projectee with | Names _0 -> true | uu____1982 -> false
let __proj__Names__item___0: 'a . 'a name_collection -> 'a btree =
  fun projectee  -> match projectee with | Names _0 -> _0
let uu___is_ImportedNames: 'a . 'a name_collection -> Prims.bool =
  fun projectee  ->
    match projectee with | ImportedNames _0 -> true | uu____2028 -> false
let __proj__ImportedNames__item___0:
  'a .
    'a name_collection ->
      (Prims.string,'a name_collection Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | ImportedNames _0 -> _0
type 'a names = 'a name_collection Prims.list[@@deriving show]
type 'a trie = {
  bindings: 'a names;
  namespaces: 'a trie names;}[@@deriving show]
let __proj__Mktrie__item__bindings: 'a . 'a trie -> 'a names =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; namespaces = __fname__namespaces;_} ->
        __fname__bindings
let __proj__Mktrie__item__namespaces: 'a . 'a trie -> 'a trie names =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; namespaces = __fname__namespaces;_} ->
        __fname__namespaces
let trie_empty: 'Auu____2148 . Prims.unit -> 'Auu____2148 trie =
  fun uu____2151  -> { bindings = []; namespaces = [] }
let rec names_find_exact:
  'a . 'a names -> Prims.string -> 'a FStar_Pervasives_Native.option =
  fun names1  ->
    fun ns  ->
      let uu____2182 =
        match names1 with
        | [] -> (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (Names bt)::names2 ->
            let uu____2232 = btree_find_exact bt ns in
            (uu____2232, (FStar_Pervasives_Native.Some names2))
        | (ImportedNames (uu____2247,names2))::more_names ->
            let uu____2264 = names_find_exact names2 ns in
            (uu____2264, (FStar_Pervasives_Native.Some more_names)) in
      match uu____2182 with
      | (result,names2) ->
          (match (result, names2) with
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some
              scopes) -> names_find_exact scopes ns
           | uu____2326 -> result)
let rec trie_descend_exact:
  'a . 'a trie -> query -> 'a trie FStar_Pervasives_Native.option =
  fun tr  ->
    fun query  ->
      match query with
      | [] -> FStar_Pervasives_Native.Some tr
      | ns::query1 ->
          let uu____2368 = names_find_exact tr.namespaces ns in
          FStar_Util.bind_opt uu____2368
            (fun scope  -> trie_descend_exact scope query1)
let rec trie_find_exact:
  'a . 'a trie -> query -> 'a FStar_Pervasives_Native.option =
  fun tr  ->
    fun query  ->
      match query with
      | [] -> failwith "Empty query in trie_find_exact"
      | name::[] -> names_find_exact tr.bindings name
      | ns::query1 ->
          let uu____2411 = names_find_exact tr.namespaces ns in
          FStar_Util.bind_opt uu____2411
            (fun scope  -> trie_find_exact scope query1)
let names_insert: 'a . 'a names -> Prims.string -> 'a -> 'a names =
  fun name_collections  ->
    fun id  ->
      fun v1  ->
        let uu____2455 =
          match name_collections with
          | (Names bt)::tl1 -> (bt, tl1)
          | uu____2493 -> (StrEmpty, name_collections) in
        match uu____2455 with
        | (bt,name_collections1) ->
            let uu____2518 =
              let uu____2521 = btree_insert_replace bt id v1 in
              Names uu____2521 in
            uu____2518 :: name_collections1
let rec namespaces_mutate:
  'a .
    'a trie names ->
      Prims.string ->
        query ->
          query ->
            ('a trie ->
               Prims.string -> query -> query -> 'a trie names -> 'a trie)
              -> ('a trie -> query -> 'a trie) -> 'a trie names
  =
  fun namespaces  ->
    fun ns  ->
      fun q  ->
        fun rev_acc1  ->
          fun mut_node  ->
            fun mut_leaf  ->
              let trie =
                let uu____2697 = names_find_exact namespaces ns in
                FStar_Util.dflt (trie_empty ()) uu____2697 in
              let uu____2708 = trie_mutate trie q rev_acc1 mut_node mut_leaf in
              names_insert namespaces ns uu____2708
and trie_mutate:
  'a .
    'a trie ->
      query ->
        query ->
          ('a trie ->
             Prims.string -> query -> query -> 'a trie names -> 'a trie)
            -> ('a trie -> query -> 'a trie) -> 'a trie
  =
  fun tr  ->
    fun q  ->
      fun rev_acc1  ->
        fun mut_node  ->
          fun mut_leaf  ->
            match q with
            | [] -> mut_leaf tr rev_acc1
            | id::q1 ->
                let ns' =
                  namespaces_mutate tr.namespaces id q1 (id :: rev_acc1)
                    mut_node mut_leaf in
                mut_node tr id q1 rev_acc1 ns'
let trie_mutate_leaf:
  'a . 'a trie -> query -> ('a trie -> query -> 'a trie) -> 'a trie =
  fun tr  ->
    fun query  ->
      trie_mutate tr query []
        (fun tr1  ->
           fun uu____2801  ->
             fun uu____2802  ->
               fun uu____2803  ->
                 fun namespaces  ->
                   let uu___168_2812 = tr1 in
                   { bindings = (uu___168_2812.bindings); namespaces })
let trie_insert: 'a . 'a trie -> query -> Prims.string -> 'a -> 'a trie =
  fun tr  ->
    fun ns_query  ->
      fun id  ->
        fun v1  ->
          trie_mutate_leaf tr ns_query
            (fun tr1  ->
               fun uu____2855  ->
                 let uu___169_2858 = tr1 in
                 let uu____2861 = names_insert tr1.bindings id v1 in
                 {
                   bindings = uu____2861;
                   namespaces = (uu___169_2858.namespaces)
                 })
let trie_import:
  'a .
    'a trie ->
      query ->
        query -> ('a trie -> 'a trie -> Prims.string -> 'a trie) -> 'a trie
  =
  fun tr  ->
    fun host_query  ->
      fun included_query  ->
        fun mutator  ->
          let label = query_to_string included_query in
          let included_trie =
            let uu____2930 = trie_descend_exact tr included_query in
            FStar_Util.dflt (trie_empty ()) uu____2930 in
          trie_mutate_leaf tr host_query
            (fun tr1  -> fun uu____2940  -> mutator tr1 included_trie label)
let trie_include: 'a . 'a trie -> query -> query -> 'a trie =
  fun tr  ->
    fun host_query  ->
      fun included_query  ->
        trie_import tr host_query included_query
          (fun tr1  ->
             fun inc  ->
               fun label  ->
                 let uu___170_2981 = tr1 in
                 {
                   bindings = ((ImportedNames (label, (inc.bindings))) ::
                     (tr1.bindings));
                   namespaces = (uu___170_2981.namespaces)
                 })
let trie_open_namespace: 'a . 'a trie -> query -> query -> 'a trie =
  fun tr  ->
    fun host_query  ->
      fun included_query  ->
        trie_import tr host_query included_query
          (fun tr1  ->
             fun inc  ->
               fun label  ->
                 let uu___171_3026 = tr1 in
                 {
                   bindings = (uu___171_3026.bindings);
                   namespaces = ((ImportedNames (label, (inc.namespaces))) ::
                     (tr1.namespaces))
                 })
let trie_add_alias: 'a . 'a trie -> Prims.string -> query -> query -> 'a trie
  =
  fun tr  ->
    fun key  ->
      fun host_query  ->
        fun included_query  ->
          trie_import tr host_query included_query
            (fun tr1  ->
               fun inc  ->
                 fun label  ->
                   trie_mutate_leaf tr1 [key]
                     (fun _ignored_overwritten_trie  ->
                        fun uu____3085  ->
                          {
                            bindings =
                              [ImportedNames (label, (inc.bindings))];
                            namespaces = []
                          }))
let names_revmap:
  'a 'b .
    ('a btree -> 'b) ->
      'a names ->
        (Prims.string Prims.list,'b) FStar_Pervasives_Native.tuple2
          Prims.list
  =
  fun fn  ->
    fun name_collections  ->
      let rec aux acc imports name_collections1 =
        FStar_List.fold_left
          (fun acc1  ->
             fun uu___167_3206  ->
               match uu___167_3206 with
               | Names bt ->
                   let uu____3228 =
                     let uu____3235 = fn bt in (imports, uu____3235) in
                   uu____3228 :: acc1
               | ImportedNames (nm,name_collections2) ->
                   aux acc1 (nm :: imports) name_collections2) acc
          name_collections1 in
      aux [] [] name_collections
let btree_find_all:
  'a .
    Prims.string FStar_Pervasives_Native.option ->
      'a btree -> (prefix_match,'a) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun prefix1  ->
    fun bt  ->
      btree_fold bt
        (fun k  ->
           fun tr  ->
             fun acc  -> ({ prefix = prefix1; completion = k }, tr) :: acc)
        []
type name_search_term =
  | NSTAll
  | NSTNone
  | NSTPrefix of Prims.string[@@deriving show]
let uu___is_NSTAll: name_search_term -> Prims.bool =
  fun projectee  ->
    match projectee with | NSTAll  -> true | uu____3327 -> false
let uu___is_NSTNone: name_search_term -> Prims.bool =
  fun projectee  ->
    match projectee with | NSTNone  -> true | uu____3332 -> false
let uu___is_NSTPrefix: name_search_term -> Prims.bool =
  fun projectee  ->
    match projectee with | NSTPrefix _0 -> true | uu____3338 -> false
let __proj__NSTPrefix__item___0: name_search_term -> Prims.string =
  fun projectee  -> match projectee with | NSTPrefix _0 -> _0
let names_find_rev:
  'a .
    'a names ->
      name_search_term ->
        (path_elem,'a) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun names1  ->
    fun id  ->
      let matching_values_per_collection_with_imports =
        match id with
        | NSTNone  -> []
        | NSTAll  ->
            names_revmap (btree_find_all FStar_Pervasives_Native.None) names1
        | NSTPrefix "" ->
            names_revmap (btree_find_all (FStar_Pervasives_Native.Some ""))
              names1
        | NSTPrefix id1 ->
            names_revmap (fun bt  -> btree_find_prefix bt id1) names1 in
      let matching_values_per_collection =
        FStar_List.map
          (fun uu____3475  ->
             match uu____3475 with
             | (imports,matches) ->
                 FStar_List.map
                   (fun uu____3523  ->
                      match uu____3523 with
                      | (segment,v1) -> ((mk_path_el imports segment), v1))
                   matches) matching_values_per_collection_with_imports in
      merge_increasing_lists_rev
        (fun uu____3541  ->
           match uu____3541 with
           | (path_el,uu____3547) -> (path_el.segment).completion)
        matching_values_per_collection
let rec trie_find_prefix':
  'a .
    'a trie ->
      path ->
        query ->
          (path,'a) FStar_Pervasives_Native.tuple2 Prims.list ->
            (path,'a) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun tr  ->
    fun path_acc  ->
      fun query  ->
        fun acc  ->
          let uu____3597 =
            match query with
            | [] -> (NSTAll, NSTAll, [])
            | id::[] -> ((NSTPrefix id), (NSTPrefix id), [])
            | ns::query1 -> ((NSTPrefix ns), NSTNone, query1) in
          match uu____3597 with
          | (ns_search_term,bindings_search_term,query1) ->
              let matching_namespaces_rev =
                names_find_rev tr.namespaces ns_search_term in
              let acc_with_recursive_bindings =
                FStar_List.fold_left
                  (fun acc1  ->
                     fun uu____3673  ->
                       match uu____3673 with
                       | (path_el,trie) ->
                           trie_find_prefix' trie (path_el :: path_acc)
                             query1 acc1) acc matching_namespaces_rev in
              let matching_bindings_rev =
                names_find_rev tr.bindings bindings_search_term in
              FStar_List.rev_map_onto
                (fun uu____3718  ->
                   match uu____3718 with
                   | (path_el,v1) ->
                       ((FStar_List.rev (path_el :: path_acc)), v1))
                matching_bindings_rev acc_with_recursive_bindings
let trie_find_prefix:
  'a .
    'a trie -> query -> (path,'a) FStar_Pervasives_Native.tuple2 Prims.list
  = fun tr  -> fun query  -> trie_find_prefix' tr [] query []
type ns_info = {
  ns_name: Prims.string;
  ns_loaded: Prims.bool;}[@@deriving show]
let __proj__Mkns_info__item__ns_name: ns_info -> Prims.string =
  fun projectee  ->
    match projectee with
    | { ns_name = __fname__ns_name; ns_loaded = __fname__ns_loaded;_} ->
        __fname__ns_name
let __proj__Mkns_info__item__ns_loaded: ns_info -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { ns_name = __fname__ns_name; ns_loaded = __fname__ns_loaded;_} ->
        __fname__ns_loaded
type mod_info =
  {
  mod_name: Prims.string;
  mod_path: Prims.string;
  mod_loaded: Prims.bool;}[@@deriving show]
let __proj__Mkmod_info__item__mod_name: mod_info -> Prims.string =
  fun projectee  ->
    match projectee with
    | { mod_name = __fname__mod_name; mod_path = __fname__mod_path;
        mod_loaded = __fname__mod_loaded;_} -> __fname__mod_name
let __proj__Mkmod_info__item__mod_path: mod_info -> Prims.string =
  fun projectee  ->
    match projectee with
    | { mod_name = __fname__mod_name; mod_path = __fname__mod_path;
        mod_loaded = __fname__mod_loaded;_} -> __fname__mod_path
let __proj__Mkmod_info__item__mod_loaded: mod_info -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { mod_name = __fname__mod_name; mod_path = __fname__mod_path;
        mod_loaded = __fname__mod_loaded;_} -> __fname__mod_loaded
let mod_name: mod_info -> Prims.string = fun md  -> md.mod_name
type mod_symbol =
  | Module of mod_info
  | Namespace of ns_info[@@deriving show]
let uu___is_Module: mod_symbol -> Prims.bool =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____3832 -> false
let __proj__Module__item___0: mod_symbol -> mod_info =
  fun projectee  -> match projectee with | Module _0 -> _0
let uu___is_Namespace: mod_symbol -> Prims.bool =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____3846 -> false
let __proj__Namespace__item___0: mod_symbol -> ns_info =
  fun projectee  -> match projectee with | Namespace _0 -> _0
type lid_symbol = FStar_Ident.lid[@@deriving show]
type symbol =
  | ModOrNs of mod_symbol
  | Lid of lid_symbol[@@deriving show]
let uu___is_ModOrNs: symbol -> Prims.bool =
  fun projectee  ->
    match projectee with | ModOrNs _0 -> true | uu____3868 -> false
let __proj__ModOrNs__item___0: symbol -> mod_symbol =
  fun projectee  -> match projectee with | ModOrNs _0 -> _0
let uu___is_Lid: symbol -> Prims.bool =
  fun projectee  ->
    match projectee with | Lid _0 -> true | uu____3882 -> false
let __proj__Lid__item___0: symbol -> lid_symbol =
  fun projectee  -> match projectee with | Lid _0 -> _0
type table = {
  tbl_lids: lid_symbol trie;
  tbl_mods: mod_symbol trie;}[@@deriving show]
let __proj__Mktable__item__tbl_lids: table -> lid_symbol trie =
  fun projectee  ->
    match projectee with
    | { tbl_lids = __fname__tbl_lids; tbl_mods = __fname__tbl_mods;_} ->
        __fname__tbl_lids
let __proj__Mktable__item__tbl_mods: table -> mod_symbol trie =
  fun projectee  ->
    match projectee with
    | { tbl_lids = __fname__tbl_lids; tbl_mods = __fname__tbl_mods;_} ->
        __fname__tbl_mods
let empty: table = { tbl_lids = (trie_empty ()); tbl_mods = (trie_empty ()) }
let insert: table -> query -> Prims.string -> lid_symbol -> table =
  fun tbl  ->
    fun host_query  ->
      fun id  ->
        fun c  ->
          let uu___172_3947 = tbl in
          let uu____3948 = trie_insert tbl.tbl_lids host_query id c in
          { tbl_lids = uu____3948; tbl_mods = (uu___172_3947.tbl_mods) }
let register_alias: table -> Prims.string -> query -> query -> table =
  fun tbl  ->
    fun key  ->
      fun host_query  ->
        fun included_query  ->
          let uu___173_3967 = tbl in
          let uu____3968 =
            trie_add_alias tbl.tbl_lids key host_query included_query in
          { tbl_lids = uu____3968; tbl_mods = (uu___173_3967.tbl_mods) }
let register_include: table -> query -> query -> table =
  fun tbl  ->
    fun host_query  ->
      fun included_query  ->
        let uu___174_3983 = tbl in
        let uu____3984 = trie_include tbl.tbl_lids host_query included_query in
        { tbl_lids = uu____3984; tbl_mods = (uu___174_3983.tbl_mods) }
let register_open: table -> Prims.bool -> query -> query -> table =
  fun tbl  ->
    fun is_module  ->
      fun host_query  ->
        fun included_query  ->
          if is_module
          then register_include tbl host_query included_query
          else
            (let uu___175_4004 = tbl in
             let uu____4005 =
               trie_open_namespace tbl.tbl_lids host_query included_query in
             { tbl_lids = uu____4005; tbl_mods = (uu___175_4004.tbl_mods) })
let register_module_path:
  table -> Prims.bool -> Prims.string -> query -> table =
  fun tbl  ->
    fun loaded  ->
      fun path  ->
        fun mod_query  ->
          let ins_ns id bindings full_name loaded1 =
            let uu____4045 =
              let uu____4052 = names_find_exact bindings id in
              (uu____4052, loaded1) in
            match uu____4045 with
            | (FStar_Pervasives_Native.None ,uu____4061) ->
                names_insert bindings id
                  (Namespace { ns_name = full_name; ns_loaded = loaded1 })
            | (FStar_Pervasives_Native.Some (Namespace
               { ns_name = uu____4066; ns_loaded = false ;_}),true ) ->
                names_insert bindings id
                  (Namespace { ns_name = full_name; ns_loaded = loaded1 })
            | (FStar_Pervasives_Native.Some uu____4071,uu____4072) ->
                bindings in
          let ins_mod id bindings full_name loaded1 =
            names_insert bindings id
              (Module
                 {
                   mod_name = full_name;
                   mod_path = path;
                   mod_loaded = loaded1
                 }) in
          let name_of_revq query =
            FStar_String.concat "." (FStar_List.rev query) in
          let ins id q revq bindings loaded1 =
            let name = name_of_revq (id :: revq) in
            match q with
            | [] -> ins_mod id bindings name loaded1
            | uu____4145 -> ins_ns id bindings name loaded1 in
          let uu___176_4151 = tbl in
          let uu____4152 =
            trie_mutate tbl.tbl_mods mod_query []
              (fun tr  ->
                 fun id  ->
                   fun q  ->
                     fun revq  ->
                       fun namespaces  ->
                         let uu___177_4174 = tr in
                         let uu____4177 = ins id q revq tr.bindings loaded in
                         { bindings = uu____4177; namespaces })
              (fun tr  -> fun uu____4188  -> tr) in
          { tbl_lids = (uu___176_4151.tbl_lids); tbl_mods = uu____4152 }
let string_of_path: path -> Prims.string =
  fun path  ->
    let uu____4195 = FStar_List.map (fun el  -> (el.segment).completion) path in
    FStar_String.concat "." uu____4195
let match_length_of_path: path -> Prims.int =
  fun path  ->
    let uu____4204 =
      FStar_List.fold_left
        (fun acc  ->
           fun elem  ->
             let uu____4238 = acc in
             match uu____4238 with
             | (acc_len,uu____4256) ->
                 (match (elem.segment).prefix with
                  | FStar_Pervasives_Native.Some prefix1 ->
                      let completion_len =
                        FStar_String.length (elem.segment).completion in
                      (((acc_len + (Prims.parse_int "1")) + completion_len),
                        (prefix1, completion_len))
                  | FStar_Pervasives_Native.None  -> acc))
        ((Prims.parse_int "0"), ("", (Prims.parse_int "0"))) path in
    match uu____4204 with
    | (length1,(last_prefix,last_completion_length)) ->
        ((length1 - (Prims.parse_int "1")) - last_completion_length) +
          (FStar_String.length last_prefix)
let first_import_of_path: path -> Prims.string FStar_Pervasives_Native.option
  =
  fun path  ->
    match path with
    | [] -> FStar_Pervasives_Native.None
    | { imports; segment = uu____4311;_}::uu____4312 ->
        FStar_List.last imports
let alist_of_ns_info:
  ns_info ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun ns_info  ->
    [("name", (FStar_Util.JsonStr (ns_info.ns_name)));
    ("loaded", (FStar_Util.JsonBool (ns_info.ns_loaded)))]
let alist_of_mod_info:
  mod_info ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun mod_info  ->
    [("name", (FStar_Util.JsonStr (mod_info.mod_name)));
    ("path", (FStar_Util.JsonStr (mod_info.mod_path)));
    ("loaded", (FStar_Util.JsonBool (mod_info.mod_loaded)))]
type completion_result =
  {
  completion_match_length: Prims.int;
  completion_candidate: Prims.string;
  completion_annotation: Prims.string;}[@@deriving show]
let __proj__Mkcompletion_result__item__completion_match_length:
  completion_result -> Prims.int =
  fun projectee  ->
    match projectee with
    | { completion_match_length = __fname__completion_match_length;
        completion_candidate = __fname__completion_candidate;
        completion_annotation = __fname__completion_annotation;_} ->
        __fname__completion_match_length
let __proj__Mkcompletion_result__item__completion_candidate:
  completion_result -> Prims.string =
  fun projectee  ->
    match projectee with
    | { completion_match_length = __fname__completion_match_length;
        completion_candidate = __fname__completion_candidate;
        completion_annotation = __fname__completion_annotation;_} ->
        __fname__completion_candidate
let __proj__Mkcompletion_result__item__completion_annotation:
  completion_result -> Prims.string =
  fun projectee  ->
    match projectee with
    | { completion_match_length = __fname__completion_match_length;
        completion_candidate = __fname__completion_candidate;
        completion_annotation = __fname__completion_annotation;_} ->
        __fname__completion_annotation
let json_of_completion_result: completion_result -> FStar_Util.json =
  fun result  ->
    FStar_Util.JsonList
      [FStar_Util.JsonInt (result.completion_match_length);
      FStar_Util.JsonStr (result.completion_annotation);
      FStar_Util.JsonStr (result.completion_candidate)]
let completion_result_of_lid:
  'Auu____4406 .
    (path,'Auu____4406) FStar_Pervasives_Native.tuple2 -> completion_result
  =
  fun uu____4414  ->
    match uu____4414 with
    | (path,_lid) ->
        let uu____4421 = match_length_of_path path in
        let uu____4422 = string_of_path path in
        let uu____4423 =
          let uu____4424 = first_import_of_path path in
          FStar_Util.dflt "" uu____4424 in
        {
          completion_match_length = uu____4421;
          completion_candidate = uu____4422;
          completion_annotation = uu____4423
        }
let completion_result_of_mod:
  Prims.string -> Prims.bool -> path -> completion_result =
  fun annot  ->
    fun loaded  ->
      fun path  ->
        let uu____4439 = match_length_of_path path in
        let uu____4440 = string_of_path path in
        let uu____4441 =
          FStar_Util.format1 (if loaded then " %s " else "(%s)") annot in
        {
          completion_match_length = uu____4439;
          completion_candidate = uu____4440;
          completion_annotation = uu____4441
        }
let completion_result_of_ns_or_mod:
  (path,mod_symbol) FStar_Pervasives_Native.tuple2 -> completion_result =
  fun uu____4450  ->
    match uu____4450 with
    | (path,symb) ->
        (match symb with
         | Module
             { mod_name = uu____4457; mod_path = uu____4458;
               mod_loaded = loaded;_}
             -> completion_result_of_mod "mod" loaded path
         | Namespace { ns_name = uu____4460; ns_loaded = loaded;_} ->
             completion_result_of_mod "ns" loaded path)
let find_module_or_ns:
  table -> query -> mod_symbol FStar_Pervasives_Native.option =
  fun tbl  -> fun query  -> trie_find_exact tbl.tbl_mods query
let autocomplete_lid: table -> query -> completion_result Prims.list =
  fun tbl  ->
    fun query  ->
      let uu____4482 = trie_find_prefix tbl.tbl_lids query in
      FStar_List.map completion_result_of_lid uu____4482
let autocomplete_mod_or_ns:
  table ->
    query ->
      ((path,mod_symbol) FStar_Pervasives_Native.tuple2 ->
         (path,mod_symbol) FStar_Pervasives_Native.tuple2
           FStar_Pervasives_Native.option)
        -> completion_result Prims.list
  =
  fun tbl  ->
    fun query  ->
      fun filter1  ->
        let uu____4532 =
          let uu____4539 = trie_find_prefix tbl.tbl_mods query in
          FStar_All.pipe_right uu____4539 (FStar_List.filter_map filter1) in
        FStar_All.pipe_right uu____4532
          (FStar_List.map completion_result_of_ns_or_mod)