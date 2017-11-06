open Prims
let string_compare: Prims.string -> Prims.string -> Prims.int =
  fun s1  -> fun s2  -> FStar_String.compare s1 s2
type 'a heap =
  | EmptyHeap
  | Heap of ('a,'a heap Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                    show]
let uu___is_EmptyHeap: 'a . 'a heap -> Prims.bool =
  fun projectee  ->
    match projectee with | EmptyHeap  -> true | uu____37 -> false
let uu___is_Heap: 'a . 'a heap -> Prims.bool =
  fun projectee  ->
    match projectee with | Heap _0 -> true | uu____60 -> false
let __proj__Heap__item___0:
  'a . 'a heap -> ('a,'a heap Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Heap _0 -> _0
let heap_merge:
  'Auu____98 .
    ('Auu____98 -> 'Auu____98 -> Prims.int) ->
      'Auu____98 heap -> 'Auu____98 heap -> 'Auu____98 heap
  =
  fun cmp  ->
    fun h1  ->
      fun h2  ->
        match (h1, h2) with
        | (EmptyHeap ,h) -> h
        | (h,EmptyHeap ) -> h
        | (Heap (v1,hh1),Heap (v2,hh2)) ->
            let uu____173 =
              let uu____174 = cmp v1 v2 in uu____174 < (Prims.parse_int "0") in
            if uu____173
            then Heap (v1, (h2 :: hh1))
            else Heap (v2, (h1 :: hh2))
let heap_insert:
  'Auu____194 .
    ('Auu____194 -> 'Auu____194 -> Prims.int) ->
      'Auu____194 heap -> 'Auu____194 -> 'Auu____194 heap
  = fun cmp  -> fun h  -> fun v1  -> heap_merge cmp (Heap (v1, [])) h
let rec heap_merge_pairs:
  'Auu____232 .
    ('Auu____232 -> 'Auu____232 -> Prims.int) ->
      'Auu____232 heap Prims.list -> 'Auu____232 heap
  =
  fun cmp  ->
    fun uu___528_252  ->
      match uu___528_252 with
      | [] -> EmptyHeap
      | h::[] -> h
      | h1::h2::hh ->
          let uu____285 = heap_merge cmp h1 h2 in
          let uu____288 = heap_merge_pairs cmp hh in
          heap_merge cmp uu____285 uu____288
let heap_peek:
  'Auu____293 .
    'Auu____293 heap -> 'Auu____293 FStar_Pervasives_Native.option
  =
  fun uu___529_301  ->
    match uu___529_301 with
    | EmptyHeap  -> FStar_Pervasives_Native.None
    | Heap (v1,uu____305) -> FStar_Pervasives_Native.Some v1
let heap_pop:
  'Auu____317 .
    ('Auu____317 -> 'Auu____317 -> Prims.int) ->
      'Auu____317 heap ->
        ('Auu____317,'Auu____317 heap) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option
  =
  fun cmp  ->
    fun uu___530_341  ->
      match uu___530_341 with
      | EmptyHeap  -> FStar_Pervasives_Native.None
      | Heap (v1,hh) ->
          let uu____364 =
            let uu____371 = heap_merge_pairs cmp hh in (v1, uu____371) in
          FStar_Pervasives_Native.Some uu____364
let heap_from_list:
  'Auu____385 .
    ('Auu____385 -> 'Auu____385 -> Prims.int) ->
      'Auu____385 Prims.list -> 'Auu____385 heap
  =
  fun cmp  ->
    fun values  -> FStar_List.fold_left (heap_insert cmp) EmptyHeap values
let push_nodup:
  'Auu____416 .
    ('Auu____416 -> Prims.string) ->
      'Auu____416 -> 'Auu____416 Prims.list -> 'Auu____416 Prims.list
  =
  fun key_fn  ->
    fun x  ->
      fun uu___531_435  ->
        match uu___531_435 with
        | [] -> [x]
        | h::t ->
            let uu____444 =
              let uu____445 =
                let uu____446 = key_fn x in
                let uu____447 = key_fn h in
                string_compare uu____446 uu____447 in
              uu____445 = (Prims.parse_int "0") in
            if uu____444 then h :: t else x :: h :: t
let rec add_priorities:
  'Auu____455 .
    Prims.int ->
      (Prims.int,'Auu____455) FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____455 Prims.list ->
          (Prims.int,'Auu____455) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun n1  ->
    fun acc  ->
      fun uu___532_481  ->
        match uu___532_481 with
        | [] -> acc
        | h::t ->
            add_priorities (n1 + (Prims.parse_int "1")) ((n1, h) :: acc) t
let merge_increasing_lists_rev:
  'a . ('a -> Prims.string) -> 'a Prims.list Prims.list -> 'a Prims.list =
  fun key_fn  ->
    fun lists  ->
      let cmp v1 v2 =
        match (v1, v2) with
        | ((uu____568,[]),uu____569) -> failwith "impossible"
        | (uu____590,(uu____591,[])) -> failwith "impossible"
        | ((pr1,h1::uu____614),(pr2,h2::uu____617)) ->
            let cmp_h =
              let uu____639 = key_fn h1 in
              let uu____640 = key_fn h2 in string_compare uu____639 uu____640 in
            if cmp_h <> (Prims.parse_int "0") then cmp_h else pr1 - pr2 in
      let rec aux lists1 acc =
        let uu____671 = heap_pop cmp lists1 in
        match uu____671 with
        | FStar_Pervasives_Native.None  -> acc
        | FStar_Pervasives_Native.Some ((pr,[]),uu____719) ->
            failwith "impossible"
        | FStar_Pervasives_Native.Some ((pr,v1::[]),lists2) ->
            let uu____809 = push_nodup key_fn v1 acc in aux lists2 uu____809
        | FStar_Pervasives_Native.Some ((pr,v1::tl1),lists2) ->
            let uu____860 = heap_insert cmp lists2 (pr, tl1) in
            let uu____877 = push_nodup key_fn v1 acc in
            aux uu____860 uu____877 in
      let lists1 = FStar_List.filter (fun x  -> x <> []) lists in
      match lists1 with
      | [] -> []
      | l::[] -> FStar_List.rev l
      | uu____904 ->
          let lists2 = add_priorities (Prims.parse_int "0") [] lists1 in
          let uu____926 = heap_from_list cmp lists2 in aux uu____926 []
type 'a btree =
  | StrEmpty
  | StrBranch of (Prims.string,'a,'a btree,'a btree)
  FStar_Pervasives_Native.tuple4[@@deriving show]
let uu___is_StrEmpty: 'a . 'a btree -> Prims.bool =
  fun projectee  ->
    match projectee with | StrEmpty  -> true | uu____975 -> false
let uu___is_StrBranch: 'a . 'a btree -> Prims.bool =
  fun projectee  ->
    match projectee with | StrBranch _0 -> true | uu____1002 -> false
let __proj__StrBranch__item___0:
  'a .
    'a btree ->
      (Prims.string,'a,'a btree,'a btree) FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | StrBranch _0 -> _0
let rec btree_to_list_rev:
  'Auu____1047 .
    'Auu____1047 btree ->
      (Prims.string,'Auu____1047) FStar_Pervasives_Native.tuple2 Prims.list
        ->
        (Prims.string,'Auu____1047) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun btree  ->
    fun acc  ->
      match btree with
      | StrEmpty  -> acc
      | StrBranch (key,value,lbt,rbt) ->
          let uu____1090 =
            let uu____1097 = btree_to_list_rev lbt acc in (key, value) ::
              uu____1097 in
          btree_to_list_rev rbt uu____1090
let rec btree_from_list:
  'Auu____1111 .
    (Prims.string,'Auu____1111) FStar_Pervasives_Native.tuple2 Prims.list ->
      Prims.int ->
        ('Auu____1111 btree,(Prims.string,'Auu____1111)
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
         let uu____1155 = btree_from_list nodes lbt_size in
         match uu____1155 with
         | (lbt,nodes_left) ->
             (match nodes_left with
              | [] -> failwith "Invalid size passed to btree_from_list"
              | (k,v1)::nodes_left1 ->
                  let uu____1239 = btree_from_list nodes_left1 rbt_size in
                  (match uu____1239 with
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
              let uu____1336 =
                let uu____1349 = btree_insert_replace lbt k v1 in
                (k', v', uu____1349, rbt) in
              StrBranch uu____1336
            else
              if cmp > (Prims.parse_int "0")
              then
                (let uu____1359 =
                   let uu____1372 = btree_insert_replace rbt k v1 in
                   (k', v', lbt, uu____1372) in
                 StrBranch uu____1359)
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
    | StrBranch (uu____1469,uu____1470,lbt,uu____1472) ->
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
            let uu____1514 =
              let uu____1527 = btree_remove lbt k in
              (k', v1, uu____1527, rbt) in
            StrBranch uu____1514
          else
            if cmp > (Prims.parse_int "0")
            then
              (let uu____1537 =
                 let uu____1550 = btree_remove rbt k in
                 (k', v1, lbt, uu____1550) in
               StrBranch uu____1537)
            else
              (match lbt with
               | StrEmpty  -> bt
               | uu____1560 ->
                   let uu____1563 = btree_extract_min rbt in
                   (match uu____1563 with
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
            let uu____1850 =
              let uu____1851 = btree_fold rbt f acc in f k v1 uu____1851 in
            btree_fold lbt f uu____1850
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
    match projectee with | Names _0 -> true | uu____1902 -> false
let __proj__Names__item___0: 'a . 'a name_collection -> 'a btree =
  fun projectee  -> match projectee with | Names _0 -> _0
let uu___is_ImportedNames: 'a . 'a name_collection -> Prims.bool =
  fun projectee  ->
    match projectee with | ImportedNames _0 -> true | uu____1944 -> false
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
let trie_empty: 'Auu____2057 . Prims.unit -> 'Auu____2057 trie =
  fun uu____2060  -> { bindings = []; namespaces = [] }
let rec names_find_exact:
  'a . 'a names -> Prims.string -> 'a FStar_Pervasives_Native.option =
  fun names1  ->
    fun ns  ->
      let uu____2088 =
        match names1 with
        | [] -> (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (Names bt)::names2 ->
            let uu____2138 = btree_find_exact bt ns in
            (uu____2138, (FStar_Pervasives_Native.Some names2))
        | (ImportedNames (uu____2153,names2))::more_names ->
            let uu____2170 = names_find_exact names2 ns in
            (uu____2170, (FStar_Pervasives_Native.Some more_names)) in
      match uu____2088 with
      | (result,names2) ->
          (match (result, names2) with
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some
              scopes) -> names_find_exact scopes ns
           | uu____2232 -> result)
let rec trie_descend_exact:
  'a . 'a trie -> query -> 'a trie FStar_Pervasives_Native.option =
  fun tr  ->
    fun query  ->
      match query with
      | [] -> FStar_Pervasives_Native.Some tr
      | ns::query1 ->
          let uu____2271 = names_find_exact tr.namespaces ns in
          FStar_Util.bind_opt uu____2271
            (fun scope  -> trie_descend_exact scope query1)
let rec trie_find_exact:
  'a . 'a trie -> query -> 'a FStar_Pervasives_Native.option =
  fun tr  ->
    fun query  ->
      match query with
      | [] -> failwith "Empty query in trie_find_exact"
      | name::[] -> names_find_exact tr.bindings name
      | ns::query1 ->
          let uu____2311 = names_find_exact tr.namespaces ns in
          FStar_Util.bind_opt uu____2311
            (fun scope  -> trie_find_exact scope query1)
let names_insert: 'a . 'a names -> Prims.string -> 'a -> 'a names =
  fun name_collections  ->
    fun id  ->
      fun v1  ->
        let uu____2351 =
          match name_collections with
          | (Names bt)::tl1 -> (bt, tl1)
          | uu____2389 -> (StrEmpty, name_collections) in
        match uu____2351 with
        | (bt,name_collections1) ->
            let uu____2414 =
              let uu____2417 = btree_insert_replace bt id v1 in
              Names uu____2417 in
            uu____2414 :: name_collections1
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
                let uu____2593 = names_find_exact namespaces ns in
                FStar_Util.dflt (trie_empty ()) uu____2593 in
              let uu____2604 = trie_mutate trie q rev_acc1 mut_node mut_leaf in
              names_insert namespaces ns uu____2604
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
           fun uu____2693  ->
             fun uu____2694  ->
               fun uu____2695  ->
                 fun namespaces  ->
                   let uu___534_2704 = tr1 in
                   { bindings = (uu___534_2704.bindings); namespaces })
let trie_insert: 'a . 'a trie -> query -> Prims.string -> 'a -> 'a trie =
  fun tr  ->
    fun ns_query  ->
      fun id  ->
        fun v1  ->
          trie_mutate_leaf tr ns_query
            (fun tr1  ->
               fun uu____2742  ->
                 let uu___535_2745 = tr1 in
                 let uu____2748 = names_insert tr1.bindings id v1 in
                 {
                   bindings = uu____2748;
                   namespaces = (uu___535_2745.namespaces)
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
          let label1 = query_to_string included_query in
          let included_trie =
            let uu____2812 = trie_descend_exact tr included_query in
            FStar_Util.dflt (trie_empty ()) uu____2812 in
          trie_mutate_leaf tr host_query
            (fun tr1  -> fun uu____2822  -> mutator tr1 included_trie label1)
let trie_include: 'a . 'a trie -> query -> query -> 'a trie =
  fun tr  ->
    fun host_query  ->
      fun included_query  ->
        trie_import tr host_query included_query
          (fun tr1  ->
             fun inc  ->
               fun label1  ->
                 let uu___536_2859 = tr1 in
                 {
                   bindings = ((ImportedNames (label1, (inc.bindings))) ::
                     (tr1.bindings));
                   namespaces = (uu___536_2859.namespaces)
                 })
let trie_open_namespace: 'a . 'a trie -> query -> query -> 'a trie =
  fun tr  ->
    fun host_query  ->
      fun included_query  ->
        trie_import tr host_query included_query
          (fun tr1  ->
             fun inc  ->
               fun label1  ->
                 let uu___537_2900 = tr1 in
                 {
                   bindings = (uu___537_2900.bindings);
                   namespaces = ((ImportedNames (label1, (inc.namespaces)))
                     :: (tr1.namespaces))
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
                 fun label1  ->
                   trie_mutate_leaf tr1 [key]
                     (fun _ignored_overwritten_trie  ->
                        fun uu____2954  ->
                          {
                            bindings =
                              [ImportedNames (label1, (inc.bindings))];
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
             fun uu___533_3071  ->
               match uu___533_3071 with
               | Names bt ->
                   let uu____3093 =
                     let uu____3100 = fn bt in (imports, uu____3100) in
                   uu____3093 :: acc1
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
    match projectee with | NSTAll  -> true | uu____3188 -> false
let uu___is_NSTNone: name_search_term -> Prims.bool =
  fun projectee  ->
    match projectee with | NSTNone  -> true | uu____3192 -> false
let uu___is_NSTPrefix: name_search_term -> Prims.bool =
  fun projectee  ->
    match projectee with | NSTPrefix _0 -> true | uu____3197 -> false
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
          (fun uu____3330  ->
             match uu____3330 with
             | (imports,matches) ->
                 FStar_List.map
                   (fun uu____3378  ->
                      match uu____3378 with
                      | (segment,v1) -> ((mk_path_el imports segment), v1))
                   matches) matching_values_per_collection_with_imports in
      merge_increasing_lists_rev
        (fun uu____3396  ->
           match uu____3396 with
           | (path_el,uu____3402) -> (path_el.segment).completion)
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
          let uu____3447 =
            match query with
            | [] -> (NSTAll, NSTAll, [])
            | id::[] -> ((NSTPrefix id), (NSTPrefix id), [])
            | ns::query1 -> ((NSTPrefix ns), NSTNone, query1) in
          match uu____3447 with
          | (ns_search_term,bindings_search_term,query1) ->
              let matching_namespaces_rev =
                names_find_rev tr.namespaces ns_search_term in
              let acc_with_recursive_bindings =
                FStar_List.fold_left
                  (fun acc1  ->
                     fun uu____3523  ->
                       match uu____3523 with
                       | (path_el,trie) ->
                           trie_find_prefix' trie (path_el :: path_acc)
                             query1 acc1) acc matching_namespaces_rev in
              let matching_bindings_rev =
                names_find_rev tr.bindings bindings_search_term in
              FStar_List.rev_map_onto
                (fun uu____3568  ->
                   match uu____3568 with
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
    match projectee with | Module _0 -> true | uu____3672 -> false
let __proj__Module__item___0: mod_symbol -> mod_info =
  fun projectee  -> match projectee with | Module _0 -> _0
let uu___is_Namespace: mod_symbol -> Prims.bool =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____3684 -> false
let __proj__Namespace__item___0: mod_symbol -> ns_info =
  fun projectee  -> match projectee with | Namespace _0 -> _0
type lid_symbol = FStar_Ident.lid[@@deriving show]
type symbol =
  | ModOrNs of mod_symbol
  | Lid of lid_symbol[@@deriving show]
let uu___is_ModOrNs: symbol -> Prims.bool =
  fun projectee  ->
    match projectee with | ModOrNs _0 -> true | uu____3704 -> false
let __proj__ModOrNs__item___0: symbol -> mod_symbol =
  fun projectee  -> match projectee with | ModOrNs _0 -> _0
let uu___is_Lid: symbol -> Prims.bool =
  fun projectee  ->
    match projectee with | Lid _0 -> true | uu____3716 -> false
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
          let uu___538_3774 = tbl in
          let uu____3775 = trie_insert tbl.tbl_lids host_query id c in
          { tbl_lids = uu____3775; tbl_mods = (uu___538_3774.tbl_mods) }
let register_alias: table -> Prims.string -> query -> query -> table =
  fun tbl  ->
    fun key  ->
      fun host_query  ->
        fun included_query  ->
          let uu___539_3790 = tbl in
          let uu____3791 =
            trie_add_alias tbl.tbl_lids key host_query included_query in
          { tbl_lids = uu____3791; tbl_mods = (uu___539_3790.tbl_mods) }
let register_include: table -> query -> query -> table =
  fun tbl  ->
    fun host_query  ->
      fun included_query  ->
        let uu___540_3803 = tbl in
        let uu____3804 = trie_include tbl.tbl_lids host_query included_query in
        { tbl_lids = uu____3804; tbl_mods = (uu___540_3803.tbl_mods) }
let register_open: table -> Prims.bool -> query -> query -> table =
  fun tbl  ->
    fun is_module  ->
      fun host_query  ->
        fun included_query  ->
          if is_module
          then register_include tbl host_query included_query
          else
            (let uu___541_3820 = tbl in
             let uu____3821 =
               trie_open_namespace tbl.tbl_lids host_query included_query in
             { tbl_lids = uu____3821; tbl_mods = (uu___541_3820.tbl_mods) })
let register_module_path:
  table -> Prims.bool -> Prims.string -> query -> table =
  fun tbl  ->
    fun loaded  ->
      fun path  ->
        fun mod_query  ->
          let ins_ns id bindings full_name loaded1 =
            let uu____3857 =
              let uu____3864 = names_find_exact bindings id in
              (uu____3864, loaded1) in
            match uu____3857 with
            | (FStar_Pervasives_Native.None ,uu____3873) ->
                names_insert bindings id
                  (Namespace { ns_name = full_name; ns_loaded = loaded1 })
            | (FStar_Pervasives_Native.Some (Namespace
               { ns_name = uu____3878; ns_loaded = false ;_}),true ) ->
                names_insert bindings id
                  (Namespace { ns_name = full_name; ns_loaded = loaded1 })
            | (FStar_Pervasives_Native.Some uu____3883,uu____3884) ->
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
            | uu____3957 -> ins_ns id bindings name loaded1 in
          let uu___542_3963 = tbl in
          let uu____3964 =
            trie_mutate tbl.tbl_mods mod_query []
              (fun tr  ->
                 fun id  ->
                   fun q  ->
                     fun revq  ->
                       fun namespaces  ->
                         let uu___543_3986 = tr in
                         let uu____3989 = ins id q revq tr.bindings loaded in
                         { bindings = uu____3989; namespaces })
              (fun tr  -> fun uu____4000  -> tr) in
          { tbl_lids = (uu___542_3963.tbl_lids); tbl_mods = uu____3964 }
let string_of_path: path -> Prims.string =
  fun path  ->
    let uu____4006 = FStar_List.map (fun el  -> (el.segment).completion) path in
    FStar_String.concat "." uu____4006
let match_length_of_path: path -> Prims.int =
  fun path  ->
    let uu____4014 =
      FStar_List.fold_left
        (fun acc  ->
           fun elem  ->
             let uu____4048 = acc in
             match uu____4048 with
             | (acc_len,uu____4066) ->
                 (match (elem.segment).prefix with
                  | FStar_Pervasives_Native.Some prefix1 ->
                      let completion_len =
                        FStar_String.length (elem.segment).completion in
                      (((acc_len + (Prims.parse_int "1")) + completion_len),
                        (prefix1, completion_len))
                  | FStar_Pervasives_Native.None  -> acc))
        ((Prims.parse_int "0"), ("", (Prims.parse_int "0"))) path in
    match uu____4014 with
    | (length1,(last_prefix,last_completion_length)) ->
        ((length1 - (Prims.parse_int "1")) - last_completion_length) +
          (FStar_String.length last_prefix)
let first_import_of_path: path -> Prims.string FStar_Pervasives_Native.option
  =
  fun path  ->
    match path with
    | [] -> FStar_Pervasives_Native.None
    | { imports; segment = uu____4120;_}::uu____4121 ->
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
  'Auu____4207 .
    (path,'Auu____4207) FStar_Pervasives_Native.tuple2 -> completion_result
  =
  fun uu____4215  ->
    match uu____4215 with
    | (path,_lid) ->
        let uu____4222 = match_length_of_path path in
        let uu____4223 = string_of_path path in
        let uu____4224 =
          let uu____4225 = first_import_of_path path in
          FStar_Util.dflt "" uu____4225 in
        {
          completion_match_length = uu____4222;
          completion_candidate = uu____4223;
          completion_annotation = uu____4224
        }
let completion_result_of_mod:
  Prims.string -> Prims.bool -> path -> completion_result =
  fun annot  ->
    fun loaded  ->
      fun path  ->
        let uu____4237 = match_length_of_path path in
        let uu____4238 = string_of_path path in
        let uu____4239 =
          FStar_Util.format1 (if loaded then " %s " else "(%s)") annot in
        {
          completion_match_length = uu____4237;
          completion_candidate = uu____4238;
          completion_annotation = uu____4239
        }
let completion_result_of_ns_or_mod:
  (path,mod_symbol) FStar_Pervasives_Native.tuple2 -> completion_result =
  fun uu____4247  ->
    match uu____4247 with
    | (path,symb) ->
        (match symb with
         | Module
             { mod_name = uu____4254; mod_path = uu____4255;
               mod_loaded = loaded;_}
             -> completion_result_of_mod "mod" loaded path
         | Namespace { ns_name = uu____4257; ns_loaded = loaded;_} ->
             completion_result_of_mod "ns" loaded path)
let find_module_or_ns:
  table -> query -> mod_symbol FStar_Pervasives_Native.option =
  fun tbl  -> fun query  -> trie_find_exact tbl.tbl_mods query
let autocomplete_lid: table -> query -> completion_result Prims.list =
  fun tbl  ->
    fun query  ->
      let uu____4275 = trie_find_prefix tbl.tbl_lids query in
      FStar_List.map completion_result_of_lid uu____4275
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
        let uu____4322 =
          let uu____4329 = trie_find_prefix tbl.tbl_mods query in
          FStar_All.pipe_right uu____4329 (FStar_List.filter_map filter1) in
        FStar_All.pipe_right uu____4322
          (FStar_List.map completion_result_of_ns_or_mod)