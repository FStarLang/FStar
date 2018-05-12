open Prims
let (string_compare : Prims.string -> Prims.string -> Prims.int) =
  fun s1  -> fun s2  -> FStar_String.compare s1 s2 
type 'a heap =
  | EmptyHeap 
  | Heap of ('a,'a heap Prims.list) FStar_Pervasives_Native.tuple2 
let uu___is_EmptyHeap : 'a . 'a heap -> Prims.bool =
  fun projectee  ->
    match projectee with | EmptyHeap  -> true | uu____45 -> false
  
let uu___is_Heap : 'a . 'a heap -> Prims.bool =
  fun projectee  ->
    match projectee with | Heap _0 -> true | uu____71 -> false
  
let __proj__Heap__item___0 :
  'a . 'a heap -> ('a,'a heap Prims.list) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Heap _0 -> _0 
let heap_merge :
  'Auu____114 .
    ('Auu____114 -> 'Auu____114 -> Prims.int) ->
      'Auu____114 heap -> 'Auu____114 heap -> 'Auu____114 heap
  =
  fun cmp  ->
    fun h1  ->
      fun h2  ->
        match (h1, h2) with
        | (EmptyHeap ,h) -> h
        | (h,EmptyHeap ) -> h
        | (Heap (v1,hh1),Heap (v2,hh2)) ->
            let uu____192 =
              let uu____193 = cmp v1 v2  in uu____193 < (Prims.parse_int "0")
               in
            if uu____192
            then Heap (v1, (h2 :: hh1))
            else Heap (v2, (h1 :: hh2))
  
let heap_insert :
  'Auu____217 .
    ('Auu____217 -> 'Auu____217 -> Prims.int) ->
      'Auu____217 heap -> 'Auu____217 -> 'Auu____217 heap
  = fun cmp  -> fun h  -> fun v1  -> heap_merge cmp (Heap (v1, [])) h 
let rec heap_merge_pairs :
  'Auu____263 .
    ('Auu____263 -> 'Auu____263 -> Prims.int) ->
      'Auu____263 heap Prims.list -> 'Auu____263 heap
  =
  fun cmp  ->
    fun uu___58_285  ->
      match uu___58_285 with
      | [] -> EmptyHeap
      | h::[] -> h
      | h1::h2::hh ->
          let uu____318 = heap_merge cmp h1 h2  in
          let uu____321 = heap_merge_pairs cmp hh  in
          heap_merge cmp uu____318 uu____321
  
let heap_peek :
  'Auu____328 .
    'Auu____328 heap -> 'Auu____328 FStar_Pervasives_Native.option
  =
  fun uu___59_337  ->
    match uu___59_337 with
    | EmptyHeap  -> FStar_Pervasives_Native.None
    | Heap (v1,uu____341) -> FStar_Pervasives_Native.Some v1
  
let heap_pop :
  'Auu____356 .
    ('Auu____356 -> 'Auu____356 -> Prims.int) ->
      'Auu____356 heap ->
        ('Auu____356,'Auu____356 heap) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option
  =
  fun cmp  ->
    fun uu___60_382  ->
      match uu___60_382 with
      | EmptyHeap  -> FStar_Pervasives_Native.None
      | Heap (v1,hh) ->
          let uu____405 =
            let uu____412 = heap_merge_pairs cmp hh  in (v1, uu____412)  in
          FStar_Pervasives_Native.Some uu____405
  
let heap_from_list :
  'Auu____429 .
    ('Auu____429 -> 'Auu____429 -> Prims.int) ->
      'Auu____429 Prims.list -> 'Auu____429 heap
  =
  fun cmp  ->
    fun values  -> FStar_List.fold_left (heap_insert cmp) EmptyHeap values
  
let push_nodup :
  'Auu____466 .
    ('Auu____466 -> Prims.string) ->
      'Auu____466 -> 'Auu____466 Prims.list -> 'Auu____466 Prims.list
  =
  fun key_fn  ->
    fun x  ->
      fun uu___61_488  ->
        match uu___61_488 with
        | [] -> [x]
        | h::t ->
            let uu____497 =
              let uu____498 =
                let uu____499 = key_fn x  in
                let uu____500 = key_fn h  in
                string_compare uu____499 uu____500  in
              uu____498 = (Prims.parse_int "0")  in
            if uu____497 then h :: t else x :: h :: t
  
let rec add_priorities :
  'Auu____513 .
    Prims.int ->
      (Prims.int,'Auu____513) FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____513 Prims.list ->
          (Prims.int,'Auu____513) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun n1  ->
    fun acc  ->
      fun uu___62_542  ->
        match uu___62_542 with
        | [] -> acc
        | h::t ->
            add_priorities (n1 + (Prims.parse_int "1")) ((n1, h) :: acc) t
  
let merge_increasing_lists_rev :
  'a . ('a -> Prims.string) -> 'a Prims.list Prims.list -> 'a Prims.list =
  fun key_fn  ->
    fun lists  ->
      let cmp v1 v2 =
        match (v1, v2) with
        | ((uu____638,[]),uu____639) -> failwith "impossible"
        | (uu____660,(uu____661,[])) -> failwith "impossible"
        | ((pr1,h1::uu____684),(pr2,h2::uu____687)) ->
            let cmp_h =
              let uu____709 = key_fn h1  in
              let uu____710 = key_fn h2  in
              string_compare uu____709 uu____710  in
            if cmp_h <> (Prims.parse_int "0") then cmp_h else pr1 - pr2
         in
      let rec aux lists1 acc =
        let uu____745 = heap_pop cmp lists1  in
        match uu____745 with
        | FStar_Pervasives_Native.None  -> acc
        | FStar_Pervasives_Native.Some ((pr,[]),uu____793) ->
            failwith "impossible"
        | FStar_Pervasives_Native.Some ((pr,v1::[]),lists2) ->
            let uu____883 = push_nodup key_fn v1 acc  in aux lists2 uu____883
        | FStar_Pervasives_Native.Some ((pr,v1::tl1),lists2) ->
            let uu____934 = heap_insert cmp lists2 (pr, tl1)  in
            let uu____951 = push_nodup key_fn v1 acc  in
            aux uu____934 uu____951
         in
      let lists1 = FStar_List.filter (fun x  -> x <> []) lists  in
      match lists1 with
      | [] -> []
      | l::[] -> FStar_List.rev l
      | uu____978 ->
          let lists2 = add_priorities (Prims.parse_int "0") [] lists1  in
          let uu____1000 = heap_from_list cmp lists2  in aux uu____1000 []
  
type 'a btree =
  | StrEmpty 
  | StrBranch of (Prims.string,'a,'a btree,'a btree)
  FStar_Pervasives_Native.tuple4 
let uu___is_StrEmpty : 'a . 'a btree -> Prims.bool =
  fun projectee  ->
    match projectee with | StrEmpty  -> true | uu____1053 -> false
  
let uu___is_StrBranch : 'a . 'a btree -> Prims.bool =
  fun projectee  ->
    match projectee with | StrBranch _0 -> true | uu____1083 -> false
  
let __proj__StrBranch__item___0 :
  'a .
    'a btree ->
      (Prims.string,'a,'a btree,'a btree) FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | StrBranch _0 -> _0 
let rec btree_to_list_rev :
  'Auu____1133 .
    'Auu____1133 btree ->
      (Prims.string,'Auu____1133) FStar_Pervasives_Native.tuple2 Prims.list
        ->
        (Prims.string,'Auu____1133) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun btree  ->
    fun acc  ->
      match btree with
      | StrEmpty  -> acc
      | StrBranch (key,value,lbt,rbt) ->
          let uu____1178 =
            let uu____1185 = btree_to_list_rev lbt acc  in (key, value) ::
              uu____1185
             in
          btree_to_list_rev rbt uu____1178
  
let rec btree_from_list :
  'Auu____1203 .
    (Prims.string,'Auu____1203) FStar_Pervasives_Native.tuple2 Prims.list ->
      Prims.int ->
        ('Auu____1203 btree,(Prims.string,'Auu____1203)
                              FStar_Pervasives_Native.tuple2 Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun nodes  ->
    fun size  ->
      if size = (Prims.parse_int "0")
      then (StrEmpty, nodes)
      else
        (let lbt_size = size / (Prims.parse_int "2")  in
         let rbt_size = (size - lbt_size) - (Prims.parse_int "1")  in
         let uu____1249 = btree_from_list nodes lbt_size  in
         match uu____1249 with
         | (lbt,nodes_left) ->
             (match nodes_left with
              | [] -> failwith "Invalid size passed to btree_from_list"
              | (k,v1)::nodes_left1 ->
                  let uu____1333 = btree_from_list nodes_left1 rbt_size  in
                  (match uu____1333 with
                   | (rbt,nodes_left2) ->
                       ((StrBranch (k, v1, lbt, rbt)), nodes_left2))))
  
let rec btree_insert_replace :
  'a . 'a btree -> Prims.string -> 'a -> 'a btree =
  fun bt  ->
    fun k  ->
      fun v1  ->
        match bt with
        | StrEmpty  -> StrBranch (k, v1, StrEmpty, StrEmpty)
        | StrBranch (k',v',lbt,rbt) ->
            let cmp = string_compare k k'  in
            if cmp < (Prims.parse_int "0")
            then
              let uu____1438 =
                let uu____1451 = btree_insert_replace lbt k v1  in
                (k', v', uu____1451, rbt)  in
              StrBranch uu____1438
            else
              if cmp > (Prims.parse_int "0")
              then
                (let uu____1461 =
                   let uu____1474 = btree_insert_replace rbt k v1  in
                   (k', v', lbt, uu____1474)  in
                 StrBranch uu____1461)
              else StrBranch (k', v1, lbt, rbt)
  
let rec btree_find_exact :
  'a . 'a btree -> Prims.string -> 'a FStar_Pervasives_Native.option =
  fun bt  ->
    fun k  ->
      match bt with
      | StrEmpty  -> FStar_Pervasives_Native.None
      | StrBranch (k',v1,lbt,rbt) ->
          let cmp = string_compare k k'  in
          if cmp < (Prims.parse_int "0")
          then btree_find_exact lbt k
          else
            if cmp > (Prims.parse_int "0")
            then btree_find_exact rbt k
            else FStar_Pervasives_Native.Some v1
  
let rec btree_extract_min :
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
    | StrBranch (uu____1581,uu____1582,lbt,uu____1584) ->
        btree_extract_min lbt
  
let rec btree_remove : 'a . 'a btree -> Prims.string -> 'a btree =
  fun bt  ->
    fun k  ->
      match bt with
      | StrEmpty  -> StrEmpty
      | StrBranch (k',v1,lbt,rbt) ->
          let cmp = string_compare k k'  in
          if cmp < (Prims.parse_int "0")
          then
            let uu____1632 =
              let uu____1645 = btree_remove lbt k  in
              (k', v1, uu____1645, rbt)  in
            StrBranch uu____1632
          else
            if cmp > (Prims.parse_int "0")
            then
              (let uu____1655 =
                 let uu____1668 = btree_remove rbt k  in
                 (k', v1, lbt, uu____1668)  in
               StrBranch uu____1655)
            else
              (match lbt with
               | StrEmpty  -> bt
               | uu____1678 ->
                   let uu____1681 = btree_extract_min rbt  in
                   (match uu____1681 with
                    | FStar_Pervasives_Native.None  -> lbt
                    | FStar_Pervasives_Native.Some (rbt_min_k,rbt_min_v,rbt')
                        -> StrBranch (rbt_min_k, rbt_min_v, lbt, rbt')))
  
type prefix_match =
  {
  prefix: Prims.string FStar_Pervasives_Native.option ;
  completion: Prims.string }
let (__proj__Mkprefix_match__item__prefix :
  prefix_match -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { prefix = __fname__prefix; completion = __fname__completion;_} ->
        __fname__prefix
  
let (__proj__Mkprefix_match__item__completion : prefix_match -> Prims.string)
  =
  fun projectee  ->
    match projectee with
    | { prefix = __fname__prefix; completion = __fname__completion;_} ->
        __fname__completion
  
type path_elem = {
  imports: Prims.string Prims.list ;
  segment: prefix_match }
let (__proj__Mkpath_elem__item__imports :
  path_elem -> Prims.string Prims.list) =
  fun projectee  ->
    match projectee with
    | { imports = __fname__imports; segment = __fname__segment;_} ->
        __fname__imports
  
let (__proj__Mkpath_elem__item__segment : path_elem -> prefix_match) =
  fun projectee  ->
    match projectee with
    | { imports = __fname__imports; segment = __fname__segment;_} ->
        __fname__segment
  
let (matched_prefix_of_path_elem :
  path_elem -> Prims.string FStar_Pervasives_Native.option) =
  fun elem  -> (elem.segment).prefix 
let (mk_path_el : Prims.string Prims.list -> prefix_match -> path_elem) =
  fun imports  -> fun segment  -> { imports; segment } 
let rec btree_find_prefix :
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
            let cmp = string_compare k prefix2  in
            let include_middle = FStar_Util.starts_with k prefix2  in
            let explore_right =
              (cmp <= (Prims.parse_int "0")) || include_middle  in
            let explore_left = cmp > (Prims.parse_int "0")  in
            let matches = if explore_right then aux rbt prefix2 acc else acc
               in
            let matches1 =
              if include_middle
              then
                ({
                   prefix = (FStar_Pervasives_Native.Some prefix2);
                   completion = k
                 }, v1)
                :: matches
              else matches  in
            let matches2 =
              if explore_left then aux lbt prefix2 matches1 else matches1  in
            matches2
         in
      aux bt prefix1 []
  
let rec btree_fold :
  'a 'b . 'a btree -> (Prims.string -> 'a -> 'b -> 'b) -> 'b -> 'b =
  fun bt  ->
    fun f  ->
      fun acc  ->
        match bt with
        | StrEmpty  -> acc
        | StrBranch (k,v1,lbt,rbt) ->
            let uu____2008 =
              let uu____2009 = btree_fold rbt f acc  in f k v1 uu____2009  in
            btree_fold lbt f uu____2008
  
type path = path_elem Prims.list
type query = Prims.string Prims.list
let (query_to_string : Prims.string Prims.list -> Prims.string) =
  fun q  -> FStar_String.concat "." q 
type 'a name_collection =
  | Names of 'a btree 
  | ImportedNames of (Prims.string,'a name_collection Prims.list)
  FStar_Pervasives_Native.tuple2 
let uu___is_Names : 'a . 'a name_collection -> Prims.bool =
  fun projectee  ->
    match projectee with | Names _0 -> true | uu____2067 -> false
  
let __proj__Names__item___0 : 'a . 'a name_collection -> 'a btree =
  fun projectee  -> match projectee with | Names _0 -> _0 
let uu___is_ImportedNames : 'a . 'a name_collection -> Prims.bool =
  fun projectee  ->
    match projectee with | ImportedNames _0 -> true | uu____2113 -> false
  
let __proj__ImportedNames__item___0 :
  'a .
    'a name_collection ->
      (Prims.string,'a name_collection Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | ImportedNames _0 -> _0 
type 'a names = 'a name_collection Prims.list
type 'a trie = {
  bindings: 'a names ;
  namespaces: 'a trie names }
let __proj__Mktrie__item__bindings : 'a . 'a trie -> 'a names =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; namespaces = __fname__namespaces;_} ->
        __fname__bindings
  
let __proj__Mktrie__item__namespaces : 'a . 'a trie -> 'a trie names =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; namespaces = __fname__namespaces;_} ->
        __fname__namespaces
  
let trie_empty : 'Auu____2236 . unit -> 'Auu____2236 trie =
  fun uu____2239  -> { bindings = []; namespaces = [] } 
let rec names_find_exact :
  'a . 'a names -> Prims.string -> 'a FStar_Pervasives_Native.option =
  fun names  ->
    fun ns  ->
      let uu____2273 =
        match names with
        | [] -> (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (Names bt)::names1 ->
            let uu____2315 = btree_find_exact bt ns  in
            (uu____2315, (FStar_Pervasives_Native.Some names1))
        | (ImportedNames (uu____2326,names1))::more_names ->
            let uu____2343 = names_find_exact names1 ns  in
            (uu____2343, (FStar_Pervasives_Native.Some more_names))
         in
      match uu____2273 with
      | (result,names1) ->
          (match (result, names1) with
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some
              scopes) -> names_find_exact scopes ns
           | uu____2391 -> result)
  
let rec trie_descend_exact :
  'a . 'a trie -> query -> 'a trie FStar_Pervasives_Native.option =
  fun tr  ->
    fun query  ->
      match query with
      | [] -> FStar_Pervasives_Native.Some tr
      | ns::query1 ->
          let uu____2434 = names_find_exact tr.namespaces ns  in
          FStar_Util.bind_opt uu____2434
            (fun scope  -> trie_descend_exact scope query1)
  
let rec trie_find_exact :
  'a . 'a trie -> query -> 'a FStar_Pervasives_Native.option =
  fun tr  ->
    fun query  ->
      match query with
      | [] -> failwith "Empty query in trie_find_exact"
      | name::[] -> names_find_exact tr.bindings name
      | ns::query1 ->
          let uu____2480 = names_find_exact tr.namespaces ns  in
          FStar_Util.bind_opt uu____2480
            (fun scope  -> trie_find_exact scope query1)
  
let names_insert : 'a . 'a names -> Prims.string -> 'a -> 'a names =
  fun name_collections  ->
    fun id1  ->
      fun v1  ->
        let uu____2527 =
          match name_collections with
          | (Names bt)::tl1 -> (bt, tl1)
          | uu____2565 -> (StrEmpty, name_collections)  in
        match uu____2527 with
        | (bt,name_collections1) ->
            let uu____2592 =
              let uu____2595 = btree_insert_replace bt id1 v1  in
              Names uu____2595  in
            uu____2592 :: name_collections1
  
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
  fun namespaces  ->
    fun ns  ->
      fun q  ->
        fun rev_acc1  ->
          fun mut_node  ->
            fun mut_leaf  ->
              let trie =
                let uu____2797 = names_find_exact namespaces ns  in
                FStar_Util.dflt (trie_empty ()) uu____2797  in
              let uu____2808 = trie_mutate trie q rev_acc1 mut_node mut_leaf
                 in
              names_insert namespaces ns uu____2808

and trie_mutate :
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
            | id1::q1 ->
                let ns' =
                  namespaces_mutate tr.namespaces id1 q1 (id1 :: rev_acc1)
                    mut_node mut_leaf
                   in
                mut_node tr id1 q1 rev_acc1 ns'

let trie_mutate_leaf :
  'a . 'a trie -> query -> ('a trie -> query -> 'a trie) -> 'a trie =
  fun tr  ->
    fun query  ->
      trie_mutate tr query []
        (fun tr1  ->
           fun uu____2905  ->
             fun uu____2906  ->
               fun uu____2907  ->
                 fun namespaces  ->
                   let uu___64_2916 = tr1  in
                   { bindings = (uu___64_2916.bindings); namespaces })
  
let trie_insert : 'a . 'a trie -> query -> Prims.string -> 'a -> 'a trie =
  fun tr  ->
    fun ns_query  ->
      fun id1  ->
        fun v1  ->
          trie_mutate_leaf tr ns_query
            (fun tr1  ->
               fun uu____2963  ->
                 let uu___65_2966 = tr1  in
                 let uu____2969 = names_insert tr1.bindings id1 v1  in
                 {
                   bindings = uu____2969;
                   namespaces = (uu___65_2966.namespaces)
                 })
  
let trie_import :
  'a .
    'a trie ->
      query ->
        query -> ('a trie -> 'a trie -> Prims.string -> 'a trie) -> 'a trie
  =
  fun tr  ->
    fun host_query  ->
      fun included_query  ->
        fun mutator  ->
          let label = query_to_string included_query  in
          let included_trie =
            let uu____3042 = trie_descend_exact tr included_query  in
            FStar_Util.dflt (trie_empty ()) uu____3042  in
          trie_mutate_leaf tr host_query
            (fun tr1  -> fun uu____3052  -> mutator tr1 included_trie label)
  
let trie_include : 'a . 'a trie -> query -> query -> 'a trie =
  fun tr  ->
    fun host_query  ->
      fun included_query  ->
        trie_import tr host_query included_query
          (fun tr1  ->
             fun inc  ->
               fun label  ->
                 let uu___66_3096 = tr1  in
                 {
                   bindings = ((ImportedNames (label, (inc.bindings))) ::
                     (tr1.bindings));
                   namespaces = (uu___66_3096.namespaces)
                 })
  
let trie_open_namespace : 'a . 'a trie -> query -> query -> 'a trie =
  fun tr  ->
    fun host_query  ->
      fun included_query  ->
        trie_import tr host_query included_query
          (fun tr1  ->
             fun inc  ->
               fun label  ->
                 let uu___67_3146 = tr1  in
                 {
                   bindings = (uu___67_3146.bindings);
                   namespaces = ((ImportedNames (label, (inc.namespaces))) ::
                     (tr1.namespaces))
                 })
  
let trie_add_alias :
  'a . 'a trie -> Prims.string -> query -> query -> 'a trie =
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
                        fun uu____3211  ->
                          {
                            bindings =
                              [ImportedNames (label, (inc.bindings))];
                            namespaces = []
                          }))
  
let names_revmap :
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
             fun uu___63_3342  ->
               match uu___63_3342 with
               | Names bt ->
                   let uu____3364 =
                     let uu____3371 = fn bt  in (imports, uu____3371)  in
                   uu____3364 :: acc1
               | ImportedNames (nm,name_collections2) ->
                   aux acc1 (nm :: imports) name_collections2) acc
          name_collections1
         in
      aux [] [] name_collections
  
let btree_find_all :
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
  | NSTPrefix of Prims.string 
let (uu___is_NSTAll : name_search_term -> Prims.bool) =
  fun projectee  ->
    match projectee with | NSTAll  -> true | uu____3467 -> false
  
let (uu___is_NSTNone : name_search_term -> Prims.bool) =
  fun projectee  ->
    match projectee with | NSTNone  -> true | uu____3473 -> false
  
let (uu___is_NSTPrefix : name_search_term -> Prims.bool) =
  fun projectee  ->
    match projectee with | NSTPrefix _0 -> true | uu____3480 -> false
  
let (__proj__NSTPrefix__item___0 : name_search_term -> Prims.string) =
  fun projectee  -> match projectee with | NSTPrefix _0 -> _0 
let names_find_rev :
  'a .
    'a names ->
      name_search_term ->
        (path_elem,'a) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun names  ->
    fun id1  ->
      let matching_values_per_collection_with_imports =
        match id1 with
        | NSTNone  -> []
        | NSTAll  ->
            names_revmap (btree_find_all FStar_Pervasives_Native.None) names
        | NSTPrefix "" ->
            names_revmap (btree_find_all (FStar_Pervasives_Native.Some ""))
              names
        | NSTPrefix id2 ->
            names_revmap (fun bt  -> btree_find_prefix bt id2) names
         in
      let matching_values_per_collection =
        FStar_List.map
          (fun uu____3618  ->
             match uu____3618 with
             | (imports,matches) ->
                 FStar_List.map
                   (fun uu____3666  ->
                      match uu____3666 with
                      | (segment,v1) -> ((mk_path_el imports segment), v1))
                   matches) matching_values_per_collection_with_imports
         in
      merge_increasing_lists_rev
        (fun uu____3684  ->
           match uu____3684 with
           | (path_el,uu____3690) -> (path_el.segment).completion)
        matching_values_per_collection
  
let rec trie_find_prefix' :
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
          let uu____3745 =
            match query with
            | [] -> (NSTAll, NSTAll, [])
            | id1::[] -> ((NSTPrefix id1), (NSTPrefix id1), [])
            | ns::query1 -> ((NSTPrefix ns), NSTNone, query1)  in
          match uu____3745 with
          | (ns_search_term,bindings_search_term,query1) ->
              let matching_namespaces_rev =
                names_find_rev tr.namespaces ns_search_term  in
              let acc_with_recursive_bindings =
                FStar_List.fold_left
                  (fun acc1  ->
                     fun uu____3807  ->
                       match uu____3807 with
                       | (path_el,trie) ->
                           trie_find_prefix' trie (path_el :: path_acc)
                             query1 acc1) acc matching_namespaces_rev
                 in
              let matching_bindings_rev =
                names_find_rev tr.bindings bindings_search_term  in
              FStar_List.rev_map_onto
                (fun uu____3852  ->
                   match uu____3852 with
                   | (path_el,v1) ->
                       ((FStar_List.rev (path_el :: path_acc)), v1))
                matching_bindings_rev acc_with_recursive_bindings
  
let trie_find_prefix :
  'a .
    'a trie -> query -> (path,'a) FStar_Pervasives_Native.tuple2 Prims.list
  = fun tr  -> fun query  -> trie_find_prefix' tr [] query [] 
type ns_info = {
  ns_name: Prims.string ;
  ns_loaded: Prims.bool }
let (__proj__Mkns_info__item__ns_name : ns_info -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { ns_name = __fname__ns_name; ns_loaded = __fname__ns_loaded;_} ->
        __fname__ns_name
  
let (__proj__Mkns_info__item__ns_loaded : ns_info -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { ns_name = __fname__ns_name; ns_loaded = __fname__ns_loaded;_} ->
        __fname__ns_loaded
  
type mod_info =
  {
  mod_name: Prims.string ;
  mod_path: Prims.string ;
  mod_loaded: Prims.bool }
let (__proj__Mkmod_info__item__mod_name : mod_info -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { mod_name = __fname__mod_name; mod_path = __fname__mod_path;
        mod_loaded = __fname__mod_loaded;_} -> __fname__mod_name
  
let (__proj__Mkmod_info__item__mod_path : mod_info -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { mod_name = __fname__mod_name; mod_path = __fname__mod_path;
        mod_loaded = __fname__mod_loaded;_} -> __fname__mod_path
  
let (__proj__Mkmod_info__item__mod_loaded : mod_info -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { mod_name = __fname__mod_name; mod_path = __fname__mod_path;
        mod_loaded = __fname__mod_loaded;_} -> __fname__mod_loaded
  
let (mod_name : mod_info -> Prims.string) = fun md  -> md.mod_name 
type mod_symbol =
  | Module of mod_info 
  | Namespace of ns_info 
let (uu___is_Module : mod_symbol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____3982 -> false
  
let (__proj__Module__item___0 : mod_symbol -> mod_info) =
  fun projectee  -> match projectee with | Module _0 -> _0 
let (uu___is_Namespace : mod_symbol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____3996 -> false
  
let (__proj__Namespace__item___0 : mod_symbol -> ns_info) =
  fun projectee  -> match projectee with | Namespace _0 -> _0 
type lid_symbol = FStar_Ident.lid
type symbol =
  | ModOrNs of mod_symbol 
  | Lid of lid_symbol 
let (uu___is_ModOrNs : symbol -> Prims.bool) =
  fun projectee  ->
    match projectee with | ModOrNs _0 -> true | uu____4020 -> false
  
let (__proj__ModOrNs__item___0 : symbol -> mod_symbol) =
  fun projectee  -> match projectee with | ModOrNs _0 -> _0 
let (uu___is_Lid : symbol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lid _0 -> true | uu____4034 -> false
  
let (__proj__Lid__item___0 : symbol -> lid_symbol) =
  fun projectee  -> match projectee with | Lid _0 -> _0 
type table = {
  tbl_lids: lid_symbol trie ;
  tbl_mods: mod_symbol trie }
let (__proj__Mktable__item__tbl_lids : table -> lid_symbol trie) =
  fun projectee  ->
    match projectee with
    | { tbl_lids = __fname__tbl_lids; tbl_mods = __fname__tbl_mods;_} ->
        __fname__tbl_lids
  
let (__proj__Mktable__item__tbl_mods : table -> mod_symbol trie) =
  fun projectee  ->
    match projectee with
    | { tbl_lids = __fname__tbl_lids; tbl_mods = __fname__tbl_mods;_} ->
        __fname__tbl_mods
  
let (empty : table) =
  { tbl_lids = (trie_empty ()); tbl_mods = (trie_empty ()) } 
let (insert : table -> query -> Prims.string -> lid_symbol -> table) =
  fun tbl  ->
    fun host_query  ->
      fun id1  ->
        fun c  ->
          let uu___68_4106 = tbl  in
          let uu____4107 = trie_insert tbl.tbl_lids host_query id1 c  in
          { tbl_lids = uu____4107; tbl_mods = (uu___68_4106.tbl_mods) }
  
let (register_alias : table -> Prims.string -> query -> query -> table) =
  fun tbl  ->
    fun key  ->
      fun host_query  ->
        fun included_query  ->
          let uu___69_4130 = tbl  in
          let uu____4131 =
            trie_add_alias tbl.tbl_lids key host_query included_query  in
          { tbl_lids = uu____4131; tbl_mods = (uu___69_4130.tbl_mods) }
  
let (register_include : table -> query -> query -> table) =
  fun tbl  ->
    fun host_query  ->
      fun included_query  ->
        let uu___70_4149 = tbl  in
        let uu____4150 = trie_include tbl.tbl_lids host_query included_query
           in
        { tbl_lids = uu____4150; tbl_mods = (uu___70_4149.tbl_mods) }
  
let (register_open : table -> Prims.bool -> query -> query -> table) =
  fun tbl  ->
    fun is_module  ->
      fun host_query  ->
        fun included_query  ->
          if is_module
          then register_include tbl host_query included_query
          else
            (let uu___71_4174 = tbl  in
             let uu____4175 =
               trie_open_namespace tbl.tbl_lids host_query included_query  in
             { tbl_lids = uu____4175; tbl_mods = (uu___71_4174.tbl_mods) })
  
let (register_module_path :
  table -> Prims.bool -> Prims.string -> query -> table) =
  fun tbl  ->
    fun loaded  ->
      fun path  ->
        fun mod_query  ->
          let ins_ns id1 bindings full_name loaded1 =
            let uu____4227 =
              let uu____4234 = names_find_exact bindings id1  in
              (uu____4234, loaded1)  in
            match uu____4227 with
            | (FStar_Pervasives_Native.None ,uu____4243) ->
                names_insert bindings id1
                  (Namespace { ns_name = full_name; ns_loaded = loaded1 })
            | (FStar_Pervasives_Native.Some (Namespace
               { ns_name = uu____4248; ns_loaded = false ;_}),true ) ->
                names_insert bindings id1
                  (Namespace { ns_name = full_name; ns_loaded = loaded1 })
            | (FStar_Pervasives_Native.Some uu____4253,uu____4254) ->
                bindings
             in
          let ins_mod id1 bindings full_name loaded1 =
            names_insert bindings id1
              (Module
                 {
                   mod_name = full_name;
                   mod_path = path;
                   mod_loaded = loaded1
                 })
             in
          let name_of_revq query =
            FStar_String.concat "." (FStar_List.rev query)  in
          let ins id1 q revq bindings loaded1 =
            let name = name_of_revq (id1 :: revq)  in
            match q with
            | [] -> ins_mod id1 bindings name loaded1
            | uu____4347 -> ins_ns id1 bindings name loaded1  in
          let uu___72_4353 = tbl  in
          let uu____4354 =
            trie_mutate tbl.tbl_mods mod_query []
              (fun tr  ->
                 fun id1  ->
                   fun q  ->
                     fun revq  ->
                       fun namespaces  ->
                         let uu___73_4376 = tr  in
                         let uu____4379 = ins id1 q revq tr.bindings loaded
                            in
                         { bindings = uu____4379; namespaces })
              (fun tr  -> fun uu____4390  -> tr)
             in
          { tbl_lids = (uu___72_4353.tbl_lids); tbl_mods = uu____4354 }
  
let (string_of_path : path -> Prims.string) =
  fun path  ->
    let uu____4398 = FStar_List.map (fun el  -> (el.segment).completion) path
       in
    FStar_String.concat "." uu____4398
  
let (match_length_of_path : path -> Prims.int) =
  fun path  ->
    let uu____4408 =
      FStar_List.fold_left
        (fun acc  ->
           fun elem  ->
             let uu____4442 = acc  in
             match uu____4442 with
             | (acc_len,uu____4460) ->
                 (match (elem.segment).prefix with
                  | FStar_Pervasives_Native.Some prefix1 ->
                      let completion_len =
                        FStar_String.length (elem.segment).completion  in
                      (((acc_len + (Prims.parse_int "1")) + completion_len),
                        (prefix1, completion_len))
                  | FStar_Pervasives_Native.None  -> acc))
        ((Prims.parse_int "0"), ("", (Prims.parse_int "0"))) path
       in
    match uu____4408 with
    | (length1,(last_prefix,last_completion_length)) ->
        ((length1 - (Prims.parse_int "1")) - last_completion_length) +
          (FStar_String.length last_prefix)
  
let (first_import_of_path :
  path -> Prims.string FStar_Pervasives_Native.option) =
  fun path  ->
    match path with
    | [] -> FStar_Pervasives_Native.None
    | { imports; segment = uu____4516;_}::uu____4517 ->
        FStar_List.last imports
  
let (alist_of_ns_info :
  ns_info ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun ns_info  ->
    [("name", (FStar_Util.JsonStr (ns_info.ns_name)));
    ("loaded", (FStar_Util.JsonBool (ns_info.ns_loaded)))]
  
let (alist_of_mod_info :
  mod_info ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun mod_info  ->
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
  fun projectee  ->
    match projectee with
    | { completion_match_length = __fname__completion_match_length;
        completion_candidate = __fname__completion_candidate;
        completion_annotation = __fname__completion_annotation;_} ->
        __fname__completion_match_length
  
let (__proj__Mkcompletion_result__item__completion_candidate :
  completion_result -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { completion_match_length = __fname__completion_match_length;
        completion_candidate = __fname__completion_candidate;
        completion_annotation = __fname__completion_annotation;_} ->
        __fname__completion_candidate
  
let (__proj__Mkcompletion_result__item__completion_annotation :
  completion_result -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { completion_match_length = __fname__completion_match_length;
        completion_candidate = __fname__completion_candidate;
        completion_annotation = __fname__completion_annotation;_} ->
        __fname__completion_annotation
  
let (json_of_completion_result : completion_result -> FStar_Util.json) =
  fun result  ->
    FStar_Util.JsonList
      [FStar_Util.JsonInt (result.completion_match_length);
      FStar_Util.JsonStr (result.completion_annotation);
      FStar_Util.JsonStr (result.completion_candidate)]
  
let completion_result_of_lid :
  'Auu____4620 .
    (path,'Auu____4620) FStar_Pervasives_Native.tuple2 -> completion_result
  =
  fun uu____4629  ->
    match uu____4629 with
    | (path,_lid) ->
        let uu____4636 = match_length_of_path path  in
        let uu____4637 = string_of_path path  in
        let uu____4638 =
          let uu____4639 = first_import_of_path path  in
          FStar_Util.dflt "" uu____4639  in
        {
          completion_match_length = uu____4636;
          completion_candidate = uu____4637;
          completion_annotation = uu____4638
        }
  
let (completion_result_of_mod :
  Prims.string -> Prims.bool -> path -> completion_result) =
  fun annot  ->
    fun loaded  ->
      fun path  ->
        let uu____4657 = match_length_of_path path  in
        let uu____4658 = string_of_path path  in
        let uu____4659 =
          FStar_Util.format1 (if loaded then " %s " else "(%s)") annot  in
        {
          completion_match_length = uu____4657;
          completion_candidate = uu____4658;
          completion_annotation = uu____4659
        }
  
let (completion_result_of_ns_or_mod :
  (path,mod_symbol) FStar_Pervasives_Native.tuple2 -> completion_result) =
  fun uu____4669  ->
    match uu____4669 with
    | (path,symb) ->
        (match symb with
         | Module
             { mod_name = uu____4676; mod_path = uu____4677;
               mod_loaded = loaded;_}
             -> completion_result_of_mod "mod" loaded path
         | Namespace { ns_name = uu____4679; ns_loaded = loaded;_} ->
             completion_result_of_mod "ns" loaded path)
  
let (find_module_or_ns :
  table -> query -> mod_symbol FStar_Pervasives_Native.option) =
  fun tbl  -> fun query  -> trie_find_exact tbl.tbl_mods query 
let (autocomplete_lid : table -> query -> completion_result Prims.list) =
  fun tbl  ->
    fun query  ->
      let uu____4705 = trie_find_prefix tbl.tbl_lids query  in
      FStar_List.map completion_result_of_lid uu____4705
  
let (autocomplete_mod_or_ns :
  table ->
    query ->
      ((path,mod_symbol) FStar_Pervasives_Native.tuple2 ->
         (path,mod_symbol) FStar_Pervasives_Native.tuple2
           FStar_Pervasives_Native.option)
        -> completion_result Prims.list)
  =
  fun tbl  ->
    fun query  ->
      fun filter1  ->
        let uu____4758 =
          let uu____4765 = trie_find_prefix tbl.tbl_mods query  in
          FStar_All.pipe_right uu____4765 (FStar_List.filter_map filter1)  in
        FStar_All.pipe_right uu____4758
          (FStar_List.map completion_result_of_ns_or_mod)
  