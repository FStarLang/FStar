open Prims
let (string_compare : Prims.string -> Prims.string -> Prims.int) =
  fun s1  -> fun s2  -> FStar_String.compare s1 s2 
type 'a heap =
  | EmptyHeap 
  | Heap of ('a * 'a heap Prims.list) 
let uu___is_EmptyHeap : 'a . 'a heap -> Prims.bool =
  fun projectee  ->
    match projectee with | EmptyHeap  -> true | uu____34605 -> false
  
let uu___is_Heap : 'a . 'a heap -> Prims.bool =
  fun projectee  ->
    match projectee with | Heap _0 -> true | uu____34635 -> false
  
let __proj__Heap__item___0 : 'a . 'a heap -> ('a * 'a heap Prims.list) =
  fun projectee  -> match projectee with | Heap _0 -> _0 
let heap_merge :
  'Auu____34681 .
    ('Auu____34681 -> 'Auu____34681 -> Prims.int) ->
      'Auu____34681 heap -> 'Auu____34681 heap -> 'Auu____34681 heap
  =
  fun cmp  ->
    fun h1  ->
      fun h2  ->
        match (h1, h2) with
        | (EmptyHeap ,h) -> h
        | (h,EmptyHeap ) -> h
        | (Heap (v1,hh1),Heap (v2,hh2)) ->
            let uu____34761 =
              let uu____34763 = cmp v1 v2  in
              uu____34763 < (Prims.parse_int "0")  in
            if uu____34761
            then Heap (v1, (h2 :: hh1))
            else Heap (v2, (h1 :: hh2))
  
let heap_insert :
  'Auu____34792 .
    ('Auu____34792 -> 'Auu____34792 -> Prims.int) ->
      'Auu____34792 heap -> 'Auu____34792 -> 'Auu____34792 heap
  = fun cmp  -> fun h  -> fun v1  -> heap_merge cmp (Heap (v1, [])) h 
let rec heap_merge_pairs :
  'Auu____34839 .
    ('Auu____34839 -> 'Auu____34839 -> Prims.int) ->
      'Auu____34839 heap Prims.list -> 'Auu____34839 heap
  =
  fun cmp  ->
    fun uu___295_34862  ->
      match uu___295_34862 with
      | [] -> EmptyHeap
      | h::[] -> h
      | h1::h2::hh ->
          let uu____34896 = heap_merge cmp h1 h2  in
          let uu____34899 = heap_merge_pairs cmp hh  in
          heap_merge cmp uu____34896 uu____34899
  
let heap_peek :
  'Auu____34907 .
    'Auu____34907 heap -> 'Auu____34907 FStar_Pervasives_Native.option
  =
  fun uu___296_34916  ->
    match uu___296_34916 with
    | EmptyHeap  -> FStar_Pervasives_Native.None
    | Heap (v1,uu____34920) -> FStar_Pervasives_Native.Some v1
  
let heap_pop :
  'Auu____34936 .
    ('Auu____34936 -> 'Auu____34936 -> Prims.int) ->
      'Auu____34936 heap ->
        ('Auu____34936 * 'Auu____34936 heap) FStar_Pervasives_Native.option
  =
  fun cmp  ->
    fun uu___297_34963  ->
      match uu___297_34963 with
      | EmptyHeap  -> FStar_Pervasives_Native.None
      | Heap (v1,hh) ->
          let uu____34987 =
            let uu____34994 = heap_merge_pairs cmp hh  in (v1, uu____34994)
             in
          FStar_Pervasives_Native.Some uu____34987
  
let heap_from_list :
  'Auu____35012 .
    ('Auu____35012 -> 'Auu____35012 -> Prims.int) ->
      'Auu____35012 Prims.list -> 'Auu____35012 heap
  =
  fun cmp  ->
    fun values  -> FStar_List.fold_left (heap_insert cmp) EmptyHeap values
  
let push_nodup :
  'Auu____35052 .
    ('Auu____35052 -> Prims.string) ->
      'Auu____35052 -> 'Auu____35052 Prims.list -> 'Auu____35052 Prims.list
  =
  fun key_fn  ->
    fun x  ->
      fun uu___298_35075  ->
        match uu___298_35075 with
        | [] -> [x]
        | h::t ->
            let uu____35085 =
              let uu____35087 =
                let uu____35089 = key_fn x  in
                let uu____35091 = key_fn h  in
                string_compare uu____35089 uu____35091  in
              uu____35087 = (Prims.parse_int "0")  in
            if uu____35085 then h :: t else x :: h :: t
  
let rec add_priorities :
  'Auu____35109 .
    Prims.int ->
      (Prims.int * 'Auu____35109) Prims.list ->
        'Auu____35109 Prims.list -> (Prims.int * 'Auu____35109) Prims.list
  =
  fun n1  ->
    fun acc  ->
      fun uu___299_35141  ->
        match uu___299_35141 with
        | [] -> acc
        | h::t ->
            add_priorities (n1 + (Prims.parse_int "1")) ((n1, h) :: acc) t
  
let merge_increasing_lists_rev :
  'a . ('a -> Prims.string) -> 'a Prims.list Prims.list -> 'a Prims.list =
  fun key_fn  ->
    fun lists  ->
      let cmp v1 v2 =
        match (v1, v2) with
        | ((uu____35253,[]),uu____35254) -> failwith "impossible"
        | (uu____35282,(uu____35283,[])) -> failwith "impossible"
        | ((pr1,h1::uu____35313),(pr2,h2::uu____35316)) ->
            let cmp_h =
              let uu____35345 = key_fn h1  in
              let uu____35347 = key_fn h2  in
              string_compare uu____35345 uu____35347  in
            if cmp_h <> (Prims.parse_int "0") then cmp_h else pr1 - pr2
         in
      let rec aux lists1 acc =
        let uu____35390 = heap_pop cmp lists1  in
        match uu____35390 with
        | FStar_Pervasives_Native.None  -> acc
        | FStar_Pervasives_Native.Some ((pr,[]),uu____35443) ->
            failwith "impossible"
        | FStar_Pervasives_Native.Some ((pr,v1::[]),lists2) ->
            let uu____35548 = push_nodup key_fn v1 acc  in
            aux lists2 uu____35548
        | FStar_Pervasives_Native.Some ((pr,v1::tl1),lists2) ->
            let uu____35606 = heap_insert cmp lists2 (pr, tl1)  in
            let uu____35626 = push_nodup key_fn v1 acc  in
            aux uu____35606 uu____35626
         in
      let lists1 = FStar_List.filter (fun x  -> x <> []) lists  in
      match lists1 with
      | [] -> []
      | l::[] -> FStar_List.rev l
      | uu____35653 ->
          let lists2 = add_priorities (Prims.parse_int "0") [] lists1  in
          let uu____35678 = heap_from_list cmp lists2  in aux uu____35678 []
  
type 'a btree =
  | StrEmpty 
  | StrBranch of (Prims.string * 'a * 'a btree * 'a btree) 
let uu___is_StrEmpty : 'a . 'a btree -> Prims.bool =
  fun projectee  ->
    match projectee with | StrEmpty  -> true | uu____35737 -> false
  
let uu___is_StrBranch : 'a . 'a btree -> Prims.bool =
  fun projectee  ->
    match projectee with | StrBranch _0 -> true | uu____35772 -> false
  
let __proj__StrBranch__item___0 :
  'a . 'a btree -> (Prims.string * 'a * 'a btree * 'a btree) =
  fun projectee  -> match projectee with | StrBranch _0 -> _0 
let rec btree_to_list_rev :
  'Auu____35826 .
    'Auu____35826 btree ->
      (Prims.string * 'Auu____35826) Prims.list ->
        (Prims.string * 'Auu____35826) Prims.list
  =
  fun btree  ->
    fun acc  ->
      match btree with
      | StrEmpty  -> acc
      | StrBranch (key,value,lbt,rbt) ->
          let uu____35876 =
            let uu____35884 = btree_to_list_rev lbt acc  in (key, value) ::
              uu____35884
             in
          btree_to_list_rev rbt uu____35876
  
let rec btree_from_list :
  'Auu____35905 .
    (Prims.string * 'Auu____35905) Prims.list ->
      Prims.int ->
        ('Auu____35905 btree * (Prims.string * 'Auu____35905) Prims.list)
  =
  fun nodes  ->
    fun size  ->
      if size = (Prims.parse_int "0")
      then (StrEmpty, nodes)
      else
        (let lbt_size = size / (Prims.parse_int "2")  in
         let rbt_size = (size - lbt_size) - (Prims.parse_int "1")  in
         let uu____35965 = btree_from_list nodes lbt_size  in
         match uu____35965 with
         | (lbt,nodes_left) ->
             (match nodes_left with
              | [] -> failwith "Invalid size passed to btree_from_list"
              | (k,v1)::nodes_left1 ->
                  let uu____36061 = btree_from_list nodes_left1 rbt_size  in
                  (match uu____36061 with
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
              let uu____36181 =
                let uu____36195 = btree_insert_replace lbt k v1  in
                (k', v', uu____36195, rbt)  in
              StrBranch uu____36181
            else
              if cmp > (Prims.parse_int "0")
              then
                (let uu____36209 =
                   let uu____36223 = btree_insert_replace rbt k v1  in
                   (k', v', lbt, uu____36223)  in
                 StrBranch uu____36209)
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
    'a btree -> (Prims.string * 'a * 'a btree) FStar_Pervasives_Native.option
  =
  fun bt  ->
    match bt with
    | StrEmpty  -> FStar_Pervasives_Native.None
    | StrBranch (k,v1,StrEmpty ,rbt) ->
        FStar_Pervasives_Native.Some (k, v1, rbt)
    | StrBranch (uu____36352,uu____36353,lbt,uu____36355) ->
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
            let uu____36413 =
              let uu____36427 = btree_remove lbt k  in
              (k', v1, uu____36427, rbt)  in
            StrBranch uu____36413
          else
            if cmp > (Prims.parse_int "0")
            then
              (let uu____36441 =
                 let uu____36455 = btree_remove rbt k  in
                 (k', v1, lbt, uu____36455)  in
               StrBranch uu____36441)
            else
              (match lbt with
               | StrEmpty  -> bt
               | uu____36467 ->
                   let uu____36470 = btree_extract_min rbt  in
                   (match uu____36470 with
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
    match projectee with | { prefix = prefix1; completion;_} -> prefix1
  
let (__proj__Mkprefix_match__item__completion : prefix_match -> Prims.string)
  =
  fun projectee  ->
    match projectee with | { prefix = prefix1; completion;_} -> completion
  
type path_elem = {
  imports: Prims.string Prims.list ;
  segment: prefix_match }
let (__proj__Mkpath_elem__item__imports :
  path_elem -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | { imports; segment;_} -> imports 
let (__proj__Mkpath_elem__item__segment : path_elem -> prefix_match) =
  fun projectee  -> match projectee with | { imports; segment;_} -> segment 
let (matched_prefix_of_path_elem :
  path_elem -> Prims.string FStar_Pervasives_Native.option) =
  fun elem  -> (elem.segment).prefix 
let (mk_path_el : Prims.string Prims.list -> prefix_match -> path_elem) =
  fun imports  -> fun segment  -> { imports; segment } 
let rec btree_find_prefix :
  'a . 'a btree -> Prims.string -> (prefix_match * 'a) Prims.list =
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
            let uu____36851 =
              let uu____36852 = btree_fold rbt f acc  in f k v1 uu____36852
               in
            btree_fold lbt f uu____36851
  
type path = path_elem Prims.list
type query = Prims.string Prims.list
let (query_to_string : Prims.string Prims.list -> Prims.string) =
  fun q  -> FStar_String.concat "." q 
type 'a name_collection =
  | Names of 'a btree 
  | ImportedNames of (Prims.string * 'a name_collection Prims.list) 
let uu___is_Names : 'a . 'a name_collection -> Prims.bool =
  fun projectee  ->
    match projectee with | Names _0 -> true | uu____36920 -> false
  
let __proj__Names__item___0 : 'a . 'a name_collection -> 'a btree =
  fun projectee  -> match projectee with | Names _0 -> _0 
let uu___is_ImportedNames : 'a . 'a name_collection -> Prims.bool =
  fun projectee  ->
    match projectee with | ImportedNames _0 -> true | uu____36972 -> false
  
let __proj__ImportedNames__item___0 :
  'a . 'a name_collection -> (Prims.string * 'a name_collection Prims.list) =
  fun projectee  -> match projectee with | ImportedNames _0 -> _0 
type 'a names = 'a name_collection Prims.list
type 'a trie = {
  bindings: 'a names ;
  namespaces: 'a trie names }
let __proj__Mktrie__item__bindings : 'a . 'a trie -> 'a names =
  fun projectee  ->
    match projectee with | { bindings; namespaces;_} -> bindings
  
let __proj__Mktrie__item__namespaces : 'a . 'a trie -> 'a trie names =
  fun projectee  ->
    match projectee with | { bindings; namespaces;_} -> namespaces
  
let trie_empty : 'Auu____37102 . unit -> 'Auu____37102 trie =
  fun uu____37105  -> { bindings = []; namespaces = [] } 
let rec names_find_exact :
  'a . 'a names -> Prims.string -> 'a FStar_Pervasives_Native.option =
  fun names  ->
    fun ns  ->
      let uu____37142 =
        match names with
        | [] -> (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (Names bt)::names1 ->
            let uu____37184 = btree_find_exact bt ns  in
            (uu____37184, (FStar_Pervasives_Native.Some names1))
        | (ImportedNames (uu____37195,names1))::more_names ->
            let uu____37214 = names_find_exact names1 ns  in
            (uu____37214, (FStar_Pervasives_Native.Some more_names))
         in
      match uu____37142 with
      | (result,names1) ->
          (match (result, names1) with
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some
              scopes) -> names_find_exact scopes ns
           | uu____37262 -> result)
  
let rec trie_descend_exact :
  'a . 'a trie -> query -> 'a trie FStar_Pervasives_Native.option =
  fun tr  ->
    fun query  ->
      match query with
      | [] -> FStar_Pervasives_Native.Some tr
      | ns::query1 ->
          let uu____37310 = names_find_exact tr.namespaces ns  in
          FStar_Util.bind_opt uu____37310
            (fun scope  -> trie_descend_exact scope query1)
  
let rec trie_find_exact :
  'a . 'a trie -> query -> 'a FStar_Pervasives_Native.option =
  fun tr  ->
    fun query  ->
      match query with
      | [] -> failwith "Empty query in trie_find_exact"
      | name::[] -> names_find_exact tr.bindings name
      | ns::query1 ->
          let uu____37365 = names_find_exact tr.namespaces ns  in
          FStar_Util.bind_opt uu____37365
            (fun scope  -> trie_find_exact scope query1)
  
let names_insert : 'a . 'a names -> Prims.string -> 'a -> 'a names =
  fun name_collections  ->
    fun id1  ->
      fun v1  ->
        let uu____37415 =
          match name_collections with
          | (Names bt)::tl1 -> (bt, tl1)
          | uu____37453 -> (StrEmpty, name_collections)  in
        match uu____37415 with
        | (bt,name_collections1) ->
            let uu____37480 =
              let uu____37483 = btree_insert_replace bt id1 v1  in
              Names uu____37483  in
            uu____37480 :: name_collections1
  
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
                let uu____37689 = names_find_exact namespaces ns  in
                FStar_Util.dflt (trie_empty ()) uu____37689  in
              let uu____37700 = trie_mutate trie q rev_acc1 mut_node mut_leaf
                 in
              names_insert namespaces ns uu____37700

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
           fun uu____37805  ->
             fun uu____37806  ->
               fun uu____37807  ->
                 fun namespaces  ->
                   let uu___674_37817 = tr1  in
                   { bindings = (uu___674_37817.bindings); namespaces })
  
let trie_insert : 'a . 'a trie -> query -> Prims.string -> 'a -> 'a trie =
  fun tr  ->
    fun ns_query  ->
      fun id1  ->
        fun v1  ->
          trie_mutate_leaf tr ns_query
            (fun tr1  ->
               fun uu____37867  ->
                 let uu___683_37870 = tr1  in
                 let uu____37873 = names_insert tr1.bindings id1 v1  in
                 {
                   bindings = uu____37873;
                   namespaces = (uu___683_37870.namespaces)
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
            let uu____37950 = trie_descend_exact tr included_query  in
            FStar_Util.dflt (trie_empty ()) uu____37950  in
          trie_mutate_leaf tr host_query
            (fun tr1  -> fun uu____37960  -> mutator tr1 included_trie label)
  
let trie_include : 'a . 'a trie -> query -> query -> 'a trie =
  fun tr  ->
    fun host_query  ->
      fun included_query  ->
        trie_import tr host_query included_query
          (fun tr1  ->
             fun inc  ->
               fun label  ->
                 let uu___701_38006 = tr1  in
                 {
                   bindings = ((ImportedNames (label, (inc.bindings))) ::
                     (tr1.bindings));
                   namespaces = (uu___701_38006.namespaces)
                 })
  
let trie_open_namespace : 'a . 'a trie -> query -> query -> 'a trie =
  fun tr  ->
    fun host_query  ->
      fun included_query  ->
        trie_import tr host_query included_query
          (fun tr1  ->
             fun inc  ->
               fun label  ->
                 let uu___710_38059 = tr1  in
                 {
                   bindings = (uu___710_38059.bindings);
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
                        fun uu____38131  ->
                          {
                            bindings =
                              [ImportedNames (label, (inc.bindings))];
                            namespaces = []
                          }))
  
let names_revmap :
  'a 'b .
    ('a btree -> 'b) -> 'a names -> (Prims.string Prims.list * 'b) Prims.list
  =
  fun fn  ->
    fun name_collections  ->
      let rec aux acc imports name_collections1 =
        FStar_List.fold_left
          (fun acc1  ->
             fun uu___300_38272  ->
               match uu___300_38272 with
               | Names bt ->
                   let uu____38296 =
                     let uu____38304 = fn bt  in (imports, uu____38304)  in
                   uu____38296 :: acc1
               | ImportedNames (nm,name_collections2) ->
                   aux acc1 (nm :: imports) name_collections2) acc
          name_collections1
         in
      aux [] [] name_collections
  
let btree_find_all :
  'a .
    Prims.string FStar_Pervasives_Native.option ->
      'a btree -> (prefix_match * 'a) Prims.list
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
    match projectee with | NSTAll  -> true | uu____38416 -> false
  
let (uu___is_NSTNone : name_search_term -> Prims.bool) =
  fun projectee  ->
    match projectee with | NSTNone  -> true | uu____38427 -> false
  
let (uu___is_NSTPrefix : name_search_term -> Prims.bool) =
  fun projectee  ->
    match projectee with | NSTPrefix _0 -> true | uu____38440 -> false
  
let (__proj__NSTPrefix__item___0 : name_search_term -> Prims.string) =
  fun projectee  -> match projectee with | NSTPrefix _0 -> _0 
let names_find_rev :
  'a . 'a names -> name_search_term -> (path_elem * 'a) Prims.list =
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
          (fun uu____38593  ->
             match uu____38593 with
             | (imports,matches) ->
                 FStar_List.map
                   (fun uu____38644  ->
                      match uu____38644 with
                      | (segment,v1) -> ((mk_path_el imports segment), v1))
                   matches) matching_values_per_collection_with_imports
         in
      merge_increasing_lists_rev
        (fun uu____38662  ->
           match uu____38662 with
           | (path_el,uu____38669) -> (path_el.segment).completion)
        matching_values_per_collection
  
let rec trie_find_prefix' :
  'a .
    'a trie ->
      path -> query -> (path * 'a) Prims.list -> (path * 'a) Prims.list
  =
  fun tr  ->
    fun path_acc  ->
      fun query  ->
        fun acc  ->
          let uu____38724 =
            match query with
            | [] -> (NSTAll, NSTAll, [])
            | id1::[] -> ((NSTPrefix id1), (NSTPrefix id1), [])
            | ns::query1 -> ((NSTPrefix ns), NSTNone, query1)  in
          match uu____38724 with
          | (ns_search_term,bindings_search_term,query1) ->
              let matching_namespaces_rev =
                names_find_rev tr.namespaces ns_search_term  in
              let acc_with_recursive_bindings =
                FStar_List.fold_left
                  (fun acc1  ->
                     fun uu____38795  ->
                       match uu____38795 with
                       | (path_el,trie) ->
                           trie_find_prefix' trie (path_el :: path_acc)
                             query1 acc1) acc matching_namespaces_rev
                 in
              let matching_bindings_rev =
                names_find_rev tr.bindings bindings_search_term  in
              FStar_List.rev_map_onto
                (fun uu____38840  ->
                   match uu____38840 with
                   | (path_el,v1) ->
                       ((FStar_List.rev (path_el :: path_acc)), v1))
                matching_bindings_rev acc_with_recursive_bindings
  
let trie_find_prefix : 'a . 'a trie -> query -> (path * 'a) Prims.list =
  fun tr  -> fun query  -> trie_find_prefix' tr [] query [] 
type ns_info = {
  ns_name: Prims.string ;
  ns_loaded: Prims.bool }
let (__proj__Mkns_info__item__ns_name : ns_info -> Prims.string) =
  fun projectee  -> match projectee with | { ns_name; ns_loaded;_} -> ns_name 
let (__proj__Mkns_info__item__ns_loaded : ns_info -> Prims.bool) =
  fun projectee  ->
    match projectee with | { ns_name; ns_loaded;_} -> ns_loaded
  
type mod_info =
  {
  mod_name: Prims.string ;
  mod_path: Prims.string ;
  mod_loaded: Prims.bool }
let (__proj__Mkmod_info__item__mod_name : mod_info -> Prims.string) =
  fun projectee  ->
    match projectee with | { mod_name; mod_path; mod_loaded;_} -> mod_name
  
let (__proj__Mkmod_info__item__mod_path : mod_info -> Prims.string) =
  fun projectee  ->
    match projectee with | { mod_name; mod_path; mod_loaded;_} -> mod_path
  
let (__proj__Mkmod_info__item__mod_loaded : mod_info -> Prims.bool) =
  fun projectee  ->
    match projectee with | { mod_name; mod_path; mod_loaded;_} -> mod_loaded
  
let (mod_name : mod_info -> Prims.string) = fun md  -> md.mod_name 
type mod_symbol =
  | Module of mod_info 
  | Namespace of ns_info 
let (uu___is_Module : mod_symbol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module _0 -> true | uu____39010 -> false
  
let (__proj__Module__item___0 : mod_symbol -> mod_info) =
  fun projectee  -> match projectee with | Module _0 -> _0 
let (uu___is_Namespace : mod_symbol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Namespace _0 -> true | uu____39030 -> false
  
let (__proj__Namespace__item___0 : mod_symbol -> ns_info) =
  fun projectee  -> match projectee with | Namespace _0 -> _0 
type lid_symbol = FStar_Ident.lid
type symbol =
  | ModOrNs of mod_symbol 
  | Lid of lid_symbol 
let (uu___is_ModOrNs : symbol -> Prims.bool) =
  fun projectee  ->
    match projectee with | ModOrNs _0 -> true | uu____39060 -> false
  
let (__proj__ModOrNs__item___0 : symbol -> mod_symbol) =
  fun projectee  -> match projectee with | ModOrNs _0 -> _0 
let (uu___is_Lid : symbol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lid _0 -> true | uu____39080 -> false
  
let (__proj__Lid__item___0 : symbol -> lid_symbol) =
  fun projectee  -> match projectee with | Lid _0 -> _0 
type table = {
  tbl_lids: lid_symbol trie ;
  tbl_mods: mod_symbol trie }
let (__proj__Mktable__item__tbl_lids : table -> lid_symbol trie) =
  fun projectee  ->
    match projectee with | { tbl_lids; tbl_mods;_} -> tbl_lids
  
let (__proj__Mktable__item__tbl_mods : table -> mod_symbol trie) =
  fun projectee  ->
    match projectee with | { tbl_lids; tbl_mods;_} -> tbl_mods
  
let (empty : table) =
  { tbl_lids = (trie_empty ()); tbl_mods = (trie_empty ()) } 
let (insert : table -> query -> Prims.string -> lid_symbol -> table) =
  fun tbl  ->
    fun host_query  ->
      fun id1  ->
        fun c  ->
          let uu___828_39160 = tbl  in
          let uu____39161 = trie_insert tbl.tbl_lids host_query id1 c  in
          { tbl_lids = uu____39161; tbl_mods = (uu___828_39160.tbl_mods) }
  
let (register_alias : table -> Prims.string -> query -> query -> table) =
  fun tbl  ->
    fun key  ->
      fun host_query  ->
        fun included_query  ->
          let uu___838_39187 = tbl  in
          let uu____39188 =
            trie_add_alias tbl.tbl_lids key host_query included_query  in
          { tbl_lids = uu____39188; tbl_mods = (uu___838_39187.tbl_mods) }
  
let (register_include : table -> query -> query -> table) =
  fun tbl  ->
    fun host_query  ->
      fun included_query  ->
        let uu___846_39207 = tbl  in
        let uu____39208 = trie_include tbl.tbl_lids host_query included_query
           in
        { tbl_lids = uu____39208; tbl_mods = (uu___846_39207.tbl_mods) }
  
let (register_open : table -> Prims.bool -> query -> query -> table) =
  fun tbl  ->
    fun is_module  ->
      fun host_query  ->
        fun included_query  ->
          if is_module
          then register_include tbl host_query included_query
          else
            (let uu___857_39237 = tbl  in
             let uu____39238 =
               trie_open_namespace tbl.tbl_lids host_query included_query  in
             { tbl_lids = uu____39238; tbl_mods = (uu___857_39237.tbl_mods) })
  
let (register_module_path :
  table -> Prims.bool -> Prims.string -> query -> table) =
  fun tbl  ->
    fun loaded  ->
      fun path  ->
        fun mod_query  ->
          let ins_ns id1 bindings full_name loaded1 =
            let uu____39301 =
              let uu____39309 = names_find_exact bindings id1  in
              (uu____39309, loaded1)  in
            match uu____39301 with
            | (FStar_Pervasives_Native.None ,uu____39319) ->
                names_insert bindings id1
                  (Namespace { ns_name = full_name; ns_loaded = loaded1 })
            | (FStar_Pervasives_Native.Some (Namespace
               { ns_name = uu____39326; ns_loaded = false ;_}),true ) ->
                names_insert bindings id1
                  (Namespace { ns_name = full_name; ns_loaded = loaded1 })
            | (FStar_Pervasives_Native.Some uu____39335,uu____39336) ->
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
            | uu____39453 -> ins_ns id1 bindings name loaded1  in
          let uu___902_39460 = tbl  in
          let uu____39461 =
            trie_mutate tbl.tbl_mods mod_query []
              (fun tr  ->
                 fun id1  ->
                   fun q  ->
                     fun revq  ->
                       fun namespaces  ->
                         let uu___911_39485 = tr  in
                         let uu____39488 = ins id1 q revq tr.bindings loaded
                            in
                         { bindings = uu____39488; namespaces })
              (fun tr  -> fun uu____39499  -> tr)
             in
          { tbl_lids = (uu___902_39460.tbl_lids); tbl_mods = uu____39461 }
  
let (string_of_path : path -> Prims.string) =
  fun path  ->
    let uu____39510 =
      FStar_List.map (fun el  -> (el.segment).completion) path  in
    FStar_String.concat "." uu____39510
  
let (match_length_of_path : path -> Prims.int) =
  fun path  ->
    let uu____39526 =
      FStar_List.fold_left
        (fun acc  ->
           fun elem  ->
             let uu____39566 = acc  in
             match uu____39566 with
             | (acc_len,uu____39588) ->
                 (match (elem.segment).prefix with
                  | FStar_Pervasives_Native.Some prefix1 ->
                      let completion_len =
                        FStar_String.length (elem.segment).completion  in
                      (((acc_len + (Prims.parse_int "1")) + completion_len),
                        (prefix1, completion_len))
                  | FStar_Pervasives_Native.None  -> acc))
        ((Prims.parse_int "0"), ("", (Prims.parse_int "0"))) path
       in
    match uu____39526 with
    | (length1,(last_prefix,last_completion_length)) ->
        ((length1 - (Prims.parse_int "1")) - last_completion_length) +
          (FStar_String.length last_prefix)
  
let (first_import_of_path :
  path -> Prims.string FStar_Pervasives_Native.option) =
  fun path  ->
    match path with
    | [] -> FStar_Pervasives_Native.None
    | { imports; segment = uu____39674;_}::uu____39675 ->
        FStar_List.last imports
  
let (alist_of_ns_info :
  ns_info -> (Prims.string * FStar_Util.json) Prims.list) =
  fun ns_info  ->
    [("name", (FStar_Util.JsonStr (ns_info.ns_name)));
    ("loaded", (FStar_Util.JsonBool (ns_info.ns_loaded)))]
  
let (alist_of_mod_info :
  mod_info -> (Prims.string * FStar_Util.json) Prims.list) =
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
    | { completion_match_length; completion_candidate;
        completion_annotation;_} -> completion_match_length
  
let (__proj__Mkcompletion_result__item__completion_candidate :
  completion_result -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { completion_match_length; completion_candidate;
        completion_annotation;_} -> completion_candidate
  
let (__proj__Mkcompletion_result__item__completion_annotation :
  completion_result -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { completion_match_length; completion_candidate;
        completion_annotation;_} -> completion_annotation
  
let (json_of_completion_result : completion_result -> FStar_Util.json) =
  fun result  ->
    FStar_Util.JsonList
      [FStar_Util.JsonInt (result.completion_match_length);
      FStar_Util.JsonStr (result.completion_annotation);
      FStar_Util.JsonStr (result.completion_candidate)]
  
let completion_result_of_lid :
  'Auu____39824 . (path * 'Auu____39824) -> completion_result =
  fun uu____39833  ->
    match uu____39833 with
    | (path,_lid) ->
        let uu____39840 = match_length_of_path path  in
        let uu____39842 = string_of_path path  in
        let uu____39844 =
          let uu____39846 = first_import_of_path path  in
          FStar_Util.dflt "" uu____39846  in
        {
          completion_match_length = uu____39840;
          completion_candidate = uu____39842;
          completion_annotation = uu____39844
        }
  
let (completion_result_of_mod :
  Prims.string -> Prims.bool -> path -> completion_result) =
  fun annot  ->
    fun loaded  ->
      fun path  ->
        let uu____39872 = match_length_of_path path  in
        let uu____39874 = string_of_path path  in
        let uu____39876 =
          FStar_Util.format1 (if loaded then " %s " else "(%s)") annot  in
        {
          completion_match_length = uu____39872;
          completion_candidate = uu____39874;
          completion_annotation = uu____39876
        }
  
let (completion_result_of_ns_or_mod :
  (path * mod_symbol) -> completion_result) =
  fun uu____39893  ->
    match uu____39893 with
    | (path,symb) ->
        (match symb with
         | Module
             { mod_name = uu____39900; mod_path = uu____39901;
               mod_loaded = loaded;_}
             -> completion_result_of_mod "mod" loaded path
         | Namespace { ns_name = uu____39907; ns_loaded = loaded;_} ->
             completion_result_of_mod "ns" loaded path)
  
let (find_module_or_ns :
  table -> query -> mod_symbol FStar_Pervasives_Native.option) =
  fun tbl  -> fun query  -> trie_find_exact tbl.tbl_mods query 
let (autocomplete_lid : table -> query -> completion_result Prims.list) =
  fun tbl  ->
    fun query  ->
      let uu____39938 = trie_find_prefix tbl.tbl_lids query  in
      FStar_List.map completion_result_of_lid uu____39938
  
let (autocomplete_mod_or_ns :
  table ->
    query ->
      ((path * mod_symbol) ->
         (path * mod_symbol) FStar_Pervasives_Native.option)
        -> completion_result Prims.list)
  =
  fun tbl  ->
    fun query  ->
      fun filter1  ->
        let uu____39992 =
          let uu____39999 = trie_find_prefix tbl.tbl_mods query  in
          FStar_All.pipe_right uu____39999 (FStar_List.filter_map filter1)
           in
        FStar_All.pipe_right uu____39992
          (FStar_List.map completion_result_of_ns_or_mod)
  