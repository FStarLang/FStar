
open Prims
open FStar_Pervasives

let string_compare : Prims.string  ->  Prims.string  ->  Prims.int = (fun s1 s2 -> (FStar_String.compare s1 s2))

type 'a heap =
| EmptyHeap
| Heap of ('a * 'a heap Prims.list)


let uu___is_EmptyHeap : 'a . 'a heap  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EmptyHeap -> begin
true
end
| uu____53 -> begin
false
end))


let uu___is_Heap : 'a . 'a heap  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Heap (_0) -> begin
true
end
| uu____83 -> begin
false
end))


let __proj__Heap__item___0 : 'a . 'a heap  ->  ('a * 'a heap Prims.list) = (fun projectee -> (match (projectee) with
| Heap (_0) -> begin
_0
end))


let heap_merge : 'Auu____129 . ('Auu____129  ->  'Auu____129  ->  Prims.int)  ->  'Auu____129 heap  ->  'Auu____129 heap  ->  'Auu____129 heap = (fun cmp h1 h2 -> (match (((h1), (h2))) with
| (EmptyHeap, h) -> begin
h
end
| (h, EmptyHeap) -> begin
h
end
| (Heap (v1, hh1), Heap (v2, hh2)) -> begin
(

let uu____209 = (

let uu____211 = (cmp v1 v2)
in (uu____211 < (Prims.parse_int "0")))
in (match (uu____209) with
| true -> begin
Heap (((v1), ((h2)::hh1)))
end
| uu____223 -> begin
Heap (((v2), ((h1)::hh2)))
end))
end))


let heap_insert : 'Auu____240 . ('Auu____240  ->  'Auu____240  ->  Prims.int)  ->  'Auu____240 heap  ->  'Auu____240  ->  'Auu____240 heap = (fun cmp h v1 -> (heap_merge cmp (Heap (((v1), ([])))) h))


let rec heap_merge_pairs : 'Auu____287 . ('Auu____287  ->  'Auu____287  ->  Prims.int)  ->  'Auu____287 heap Prims.list  ->  'Auu____287 heap = (fun cmp uu___87_310 -> (match (uu___87_310) with
| [] -> begin
EmptyHeap
end
| (h)::[] -> begin
h
end
| (h1)::(h2)::hh -> begin
(

let uu____344 = (heap_merge cmp h1 h2)
in (

let uu____347 = (heap_merge_pairs cmp hh)
in (heap_merge cmp uu____344 uu____347)))
end))


let heap_peek : 'Auu____355 . 'Auu____355 heap  ->  'Auu____355 FStar_Pervasives_Native.option = (fun uu___88_364 -> (match (uu___88_364) with
| EmptyHeap -> begin
FStar_Pervasives_Native.None
end
| Heap (v1, uu____368) -> begin
FStar_Pervasives_Native.Some (v1)
end))


let heap_pop : 'Auu____384 . ('Auu____384  ->  'Auu____384  ->  Prims.int)  ->  'Auu____384 heap  ->  ('Auu____384 * 'Auu____384 heap) FStar_Pervasives_Native.option = (fun cmp uu___89_411 -> (match (uu___89_411) with
| EmptyHeap -> begin
FStar_Pervasives_Native.None
end
| Heap (v1, hh) -> begin
(

let uu____435 = (

let uu____442 = (heap_merge_pairs cmp hh)
in ((v1), (uu____442)))
in FStar_Pervasives_Native.Some (uu____435))
end))


let heap_from_list : 'Auu____460 . ('Auu____460  ->  'Auu____460  ->  Prims.int)  ->  'Auu____460 Prims.list  ->  'Auu____460 heap = (fun cmp values -> (FStar_List.fold_left (heap_insert cmp) EmptyHeap values))


let push_nodup : 'Auu____500 . ('Auu____500  ->  Prims.string)  ->  'Auu____500  ->  'Auu____500 Prims.list  ->  'Auu____500 Prims.list = (fun key_fn x uu___90_523 -> (match (uu___90_523) with
| [] -> begin
(x)::[]
end
| (h)::t -> begin
(

let uu____533 = (

let uu____535 = (

let uu____537 = (key_fn x)
in (

let uu____539 = (key_fn h)
in (string_compare uu____537 uu____539)))
in (Prims.op_Equality uu____535 (Prims.parse_int "0")))
in (match (uu____533) with
| true -> begin
(h)::t
end
| uu____546 -> begin
(x)::(h)::t
end))
end))


let rec add_priorities : 'Auu____557 . Prims.int  ->  (Prims.int * 'Auu____557) Prims.list  ->  'Auu____557 Prims.list  ->  (Prims.int * 'Auu____557) Prims.list = (fun n1 acc uu___91_589 -> (match (uu___91_589) with
| [] -> begin
acc
end
| (h)::t -> begin
(add_priorities (n1 + (Prims.parse_int "1")) ((((n1), (h)))::acc) t)
end))


let merge_increasing_lists_rev : 'a . ('a  ->  Prims.string)  ->  'a Prims.list Prims.list  ->  'a Prims.list = (fun key_fn lists -> (

let cmp = (fun v1 v2 -> (match (((v1), (v2))) with
| ((uu____701, []), uu____702) -> begin
(failwith "impossible")
end
| (uu____730, (uu____731, [])) -> begin
(failwith "impossible")
end
| ((pr1, (h1)::uu____761), (pr2, (h2)::uu____764)) -> begin
(

let cmp_h = (

let uu____793 = (key_fn h1)
in (

let uu____795 = (key_fn h2)
in (string_compare uu____793 uu____795)))
in (match ((Prims.op_disEquality cmp_h (Prims.parse_int "0"))) with
| true -> begin
cmp_h
end
| uu____801 -> begin
(pr1 - pr2)
end))
end))
in (

let rec aux = (fun lists1 acc -> (

let uu____838 = (heap_pop cmp lists1)
in (match (uu____838) with
| FStar_Pervasives_Native.None -> begin
acc
end
| FStar_Pervasives_Native.Some ((pr, []), uu____891) -> begin
(failwith "impossible")
end
| FStar_Pervasives_Native.Some ((pr, (v1)::[]), lists2) -> begin
(

let uu____996 = (push_nodup key_fn v1 acc)
in (aux lists2 uu____996))
end
| FStar_Pervasives_Native.Some ((pr, (v1)::tl1), lists2) -> begin
(

let uu____1054 = (heap_insert cmp lists2 ((pr), (tl1)))
in (

let uu____1074 = (push_nodup key_fn v1 acc)
in (aux uu____1054 uu____1074)))
end)))
in (

let lists1 = (FStar_List.filter (fun x -> (Prims.op_disEquality x [])) lists)
in (match (lists1) with
| [] -> begin
[]
end
| (l)::[] -> begin
(FStar_List.rev l)
end
| uu____1101 -> begin
(

let lists2 = (add_priorities (Prims.parse_int "0") [] lists1)
in (

let uu____1126 = (heap_from_list cmp lists2)
in (aux uu____1126 [])))
end)))))

type 'a btree =
| StrEmpty
| StrBranch of (Prims.string * 'a * 'a btree * 'a btree)


let uu___is_StrEmpty : 'a . 'a btree  ->  Prims.bool = (fun projectee -> (match (projectee) with
| StrEmpty -> begin
true
end
| uu____1185 -> begin
false
end))


let uu___is_StrBranch : 'a . 'a btree  ->  Prims.bool = (fun projectee -> (match (projectee) with
| StrBranch (_0) -> begin
true
end
| uu____1220 -> begin
false
end))


let __proj__StrBranch__item___0 : 'a . 'a btree  ->  (Prims.string * 'a * 'a btree * 'a btree) = (fun projectee -> (match (projectee) with
| StrBranch (_0) -> begin
_0
end))


let rec btree_to_list_rev : 'Auu____1274 . 'Auu____1274 btree  ->  (Prims.string * 'Auu____1274) Prims.list  ->  (Prims.string * 'Auu____1274) Prims.list = (fun btree acc -> (match (btree) with
| StrEmpty -> begin
acc
end
| StrBranch (key, value, lbt, rbt) -> begin
(

let uu____1324 = (

let uu____1332 = (btree_to_list_rev lbt acc)
in (((key), (value)))::uu____1332)
in (btree_to_list_rev rbt uu____1324))
end))


let rec btree_from_list : 'Auu____1353 . (Prims.string * 'Auu____1353) Prims.list  ->  Prims.int  ->  ('Auu____1353 btree * (Prims.string * 'Auu____1353) Prims.list) = (fun nodes size -> (match ((Prims.op_Equality size (Prims.parse_int "0"))) with
| true -> begin
((StrEmpty), (nodes))
end
| uu____1405 -> begin
(

let lbt_size = (size / (Prims.parse_int "2"))
in (

let rbt_size = ((size - lbt_size) - (Prims.parse_int "1"))
in (

let uu____1413 = (btree_from_list nodes lbt_size)
in (match (uu____1413) with
| (lbt, nodes_left) -> begin
(match (nodes_left) with
| [] -> begin
(failwith "Invalid size passed to btree_from_list")
end
| ((k, v1))::nodes_left1 -> begin
(

let uu____1509 = (btree_from_list nodes_left1 rbt_size)
in (match (uu____1509) with
| (rbt, nodes_left2) -> begin
((StrBranch (((k), (v1), (lbt), (rbt)))), (nodes_left2))
end))
end)
end))))
end))


let rec btree_insert_replace : 'a . 'a btree  ->  Prims.string  ->  'a  ->  'a btree = (fun bt k v1 -> (match (bt) with
| StrEmpty -> begin
StrBranch (((k), (v1), (StrEmpty), (StrEmpty)))
end
| StrBranch (k', v', lbt, rbt) -> begin
(

let cmp = (string_compare k k')
in (match ((cmp < (Prims.parse_int "0"))) with
| true -> begin
(

let uu____1629 = (

let uu____1643 = (btree_insert_replace lbt k v1)
in ((k'), (v'), (uu____1643), (rbt)))
in StrBranch (uu____1629))
end
| uu____1651 -> begin
(match ((cmp > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____1657 = (

let uu____1671 = (btree_insert_replace rbt k v1)
in ((k'), (v'), (lbt), (uu____1671)))
in StrBranch (uu____1657))
end
| uu____1679 -> begin
StrBranch (((k'), (v1), (lbt), (rbt)))
end)
end))
end))


let rec btree_find_exact : 'a . 'a btree  ->  Prims.string  ->  'a FStar_Pervasives_Native.option = (fun bt k -> (match (bt) with
| StrEmpty -> begin
FStar_Pervasives_Native.None
end
| StrBranch (k', v1, lbt, rbt) -> begin
(

let cmp = (string_compare k k')
in (match ((cmp < (Prims.parse_int "0"))) with
| true -> begin
(btree_find_exact lbt k)
end
| uu____1733 -> begin
(match ((cmp > (Prims.parse_int "0"))) with
| true -> begin
(btree_find_exact rbt k)
end
| uu____1739 -> begin
FStar_Pervasives_Native.Some (v1)
end)
end))
end))


let rec btree_extract_min : 'a . 'a btree  ->  (Prims.string * 'a * 'a btree) FStar_Pervasives_Native.option = (fun bt -> (match (bt) with
| StrEmpty -> begin
FStar_Pervasives_Native.None
end
| StrBranch (k, v1, StrEmpty, rbt) -> begin
FStar_Pervasives_Native.Some (((k), (v1), (rbt)))
end
| StrBranch (uu____1800, uu____1801, lbt, uu____1803) -> begin
(btree_extract_min lbt)
end))


let rec btree_remove : 'a . 'a btree  ->  Prims.string  ->  'a btree = (fun bt k -> (match (bt) with
| StrEmpty -> begin
StrEmpty
end
| StrBranch (k', v1, lbt, rbt) -> begin
(

let cmp = (string_compare k k')
in (match ((cmp < (Prims.parse_int "0"))) with
| true -> begin
(

let uu____1861 = (

let uu____1875 = (btree_remove lbt k)
in ((k'), (v1), (uu____1875), (rbt)))
in StrBranch (uu____1861))
end
| uu____1883 -> begin
(match ((cmp > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____1889 = (

let uu____1903 = (btree_remove rbt k)
in ((k'), (v1), (lbt), (uu____1903)))
in StrBranch (uu____1889))
end
| uu____1911 -> begin
(match (lbt) with
| StrEmpty -> begin
bt
end
| uu____1915 -> begin
(

let uu____1918 = (btree_extract_min rbt)
in (match (uu____1918) with
| FStar_Pervasives_Native.None -> begin
lbt
end
| FStar_Pervasives_Native.Some (rbt_min_k, rbt_min_v, rbt') -> begin
StrBranch (((rbt_min_k), (rbt_min_v), (lbt), (rbt')))
end))
end)
end)
end))
end))

type prefix_match =
{prefix : Prims.string FStar_Pervasives_Native.option; completion : Prims.string}


let __proj__Mkprefix_match__item__prefix : prefix_match  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {prefix = prefix1; completion = completion} -> begin
prefix1
end))


let __proj__Mkprefix_match__item__completion : prefix_match  ->  Prims.string = (fun projectee -> (match (projectee) with
| {prefix = prefix1; completion = completion} -> begin
completion
end))

type path_elem =
{imports : Prims.string Prims.list; segment : prefix_match}


let __proj__Mkpath_elem__item__imports : path_elem  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| {imports = imports; segment = segment} -> begin
imports
end))


let __proj__Mkpath_elem__item__segment : path_elem  ->  prefix_match = (fun projectee -> (match (projectee) with
| {imports = imports; segment = segment} -> begin
segment
end))


let matched_prefix_of_path_elem : path_elem  ->  Prims.string FStar_Pervasives_Native.option = (fun elem -> elem.segment.prefix)


let mk_path_el : Prims.string Prims.list  ->  prefix_match  ->  path_elem = (fun imports segment -> {imports = imports; segment = segment})


let rec btree_find_prefix : 'a . 'a btree  ->  Prims.string  ->  (prefix_match * 'a) Prims.list = (fun bt prefix1 -> (

let rec aux = (fun bt1 prefix2 acc -> (match (bt1) with
| StrEmpty -> begin
acc
end
| StrBranch (k, v1, lbt, rbt) -> begin
(

let cmp = (string_compare k prefix2)
in (

let include_middle = (FStar_Util.starts_with k prefix2)
in (

let explore_right = ((cmp <= (Prims.parse_int "0")) || include_middle)
in (

let explore_left = (cmp > (Prims.parse_int "0"))
in (

let matches = (match (explore_right) with
| true -> begin
(aux rbt prefix2 acc)
end
| uu____2192 -> begin
acc
end)
in (

let matches1 = (match (include_middle) with
| true -> begin
((({prefix = FStar_Pervasives_Native.Some (prefix2); completion = k}), (v1)))::matches
end
| uu____2213 -> begin
matches
end)
in (

let matches2 = (match (explore_left) with
| true -> begin
(aux lbt prefix2 matches1)
end
| uu____2229 -> begin
matches1
end)
in matches2)))))))
end))
in (aux bt prefix1 [])))


let rec btree_fold : 'a 'b . 'a btree  ->  (Prims.string  ->  'a  ->  'b  ->  'b)  ->  'b  ->  'b = (fun bt f acc -> (match (bt) with
| StrEmpty -> begin
acc
end
| StrBranch (k, v1, lbt, rbt) -> begin
(

let uu____2299 = (

let uu____2300 = (btree_fold rbt f acc)
in (f k v1 uu____2300))
in (btree_fold lbt f uu____2299))
end))


type path =
path_elem Prims.list


type query =
Prims.string Prims.list


let query_to_string : Prims.string Prims.list  ->  Prims.string = (fun q -> (FStar_String.concat "." q))

type 'a name_collection =
| Names of 'a btree
| ImportedNames of (Prims.string * 'a name_collection Prims.list)


let uu___is_Names : 'a . 'a name_collection  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Names (_0) -> begin
true
end
| uu____2368 -> begin
false
end))


let __proj__Names__item___0 : 'a . 'a name_collection  ->  'a btree = (fun projectee -> (match (projectee) with
| Names (_0) -> begin
_0
end))


let uu___is_ImportedNames : 'a . 'a name_collection  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ImportedNames (_0) -> begin
true
end
| uu____2420 -> begin
false
end))


let __proj__ImportedNames__item___0 : 'a . 'a name_collection  ->  (Prims.string * 'a name_collection Prims.list) = (fun projectee -> (match (projectee) with
| ImportedNames (_0) -> begin
_0
end))


type 'a names =
'a name_collection Prims.list

type 'a trie =
{bindings : 'a names; namespaces : 'a trie names}


let __proj__Mktrie__item__bindings : 'a . 'a trie  ->  'a names = (fun projectee -> (match (projectee) with
| {bindings = bindings; namespaces = namespaces} -> begin
bindings
end))


let __proj__Mktrie__item__namespaces : 'a . 'a trie  ->  'a trie names = (fun projectee -> (match (projectee) with
| {bindings = bindings; namespaces = namespaces} -> begin
namespaces
end))


let trie_empty : 'Auu____2550 . unit  ->  'Auu____2550 trie = (fun uu____2553 -> {bindings = []; namespaces = []})


let rec names_find_exact : 'a . 'a names  ->  Prims.string  ->  'a FStar_Pervasives_Native.option = (fun names ns -> (

let uu____2590 = (match (names) with
| [] -> begin
((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
end
| (Names (bt))::names1 -> begin
(

let uu____2632 = (btree_find_exact bt ns)
in ((uu____2632), (FStar_Pervasives_Native.Some (names1))))
end
| (ImportedNames (uu____2643, names1))::more_names -> begin
(

let uu____2662 = (names_find_exact names1 ns)
in ((uu____2662), (FStar_Pervasives_Native.Some (more_names))))
end)
in (match (uu____2590) with
| (result, names1) -> begin
(match (((result), (names1))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (scopes)) -> begin
(names_find_exact scopes ns)
end
| uu____2710 -> begin
result
end)
end)))


let rec trie_descend_exact : 'a . 'a trie  ->  query  ->  'a trie FStar_Pervasives_Native.option = (fun tr query -> (match (query) with
| [] -> begin
FStar_Pervasives_Native.Some (tr)
end
| (ns)::query1 -> begin
(

let uu____2758 = (names_find_exact tr.namespaces ns)
in (FStar_Util.bind_opt uu____2758 (fun scope -> (trie_descend_exact scope query1))))
end))


let rec trie_find_exact : 'a . 'a trie  ->  query  ->  'a FStar_Pervasives_Native.option = (fun tr query -> (match (query) with
| [] -> begin
(failwith "Empty query in trie_find_exact")
end
| (name)::[] -> begin
(names_find_exact tr.bindings name)
end
| (ns)::query1 -> begin
(

let uu____2813 = (names_find_exact tr.namespaces ns)
in (FStar_Util.bind_opt uu____2813 (fun scope -> (trie_find_exact scope query1))))
end))


let names_insert : 'a . 'a names  ->  Prims.string  ->  'a  ->  'a names = (fun name_collections id1 v1 -> (

let uu____2863 = (match (name_collections) with
| (Names (bt))::tl1 -> begin
((bt), (tl1))
end
| uu____2901 -> begin
((StrEmpty), (name_collections))
end)
in (match (uu____2863) with
| (bt, name_collections1) -> begin
(

let uu____2928 = (

let uu____2931 = (btree_insert_replace bt id1 v1)
in Names (uu____2931))
in (uu____2928)::name_collections1)
end)))


let rec namespaces_mutate : 'a . 'a trie names  ->  Prims.string  ->  query  ->  query  ->  ('a trie  ->  Prims.string  ->  query  ->  query  ->  'a trie names  ->  'a trie)  ->  ('a trie  ->  query  ->  'a trie)  ->  'a trie names = (fun namespaces ns q rev_acc1 mut_node mut_leaf -> (

let trie = (

let uu____3137 = (names_find_exact namespaces ns)
in (FStar_Util.dflt (trie_empty ()) uu____3137))
in (

let uu____3148 = (trie_mutate trie q rev_acc1 mut_node mut_leaf)
in (names_insert namespaces ns uu____3148))))
and trie_mutate : 'a . 'a trie  ->  query  ->  query  ->  ('a trie  ->  Prims.string  ->  query  ->  query  ->  'a trie names  ->  'a trie)  ->  ('a trie  ->  query  ->  'a trie)  ->  'a trie = (fun tr q rev_acc1 mut_node mut_leaf -> (match (q) with
| [] -> begin
(mut_leaf tr rev_acc1)
end
| (id1)::q1 -> begin
(

let ns' = (namespaces_mutate tr.namespaces id1 q1 ((id1)::rev_acc1) mut_node mut_leaf)
in (mut_node tr id1 q1 rev_acc1 ns'))
end))


let trie_mutate_leaf : 'a . 'a trie  ->  query  ->  ('a trie  ->  query  ->  'a trie)  ->  'a trie = (fun tr query -> (trie_mutate tr query [] (fun tr1 uu____3253 uu____3254 uu____3255 namespaces -> (

let uu___93_3265 = tr1
in {bindings = uu___93_3265.bindings; namespaces = namespaces}))))


let trie_insert : 'a . 'a trie  ->  query  ->  Prims.string  ->  'a  ->  'a trie = (fun tr ns_query id1 v1 -> (trie_mutate_leaf tr ns_query (fun tr1 uu____3315 -> (

let uu___94_3318 = tr1
in (

let uu____3321 = (names_insert tr1.bindings id1 v1)
in {bindings = uu____3321; namespaces = uu___94_3318.namespaces})))))


let trie_import : 'a . 'a trie  ->  query  ->  query  ->  ('a trie  ->  'a trie  ->  Prims.string  ->  'a trie)  ->  'a trie = (fun tr host_query included_query mutator -> (

let label = (query_to_string included_query)
in (

let included_trie = (

let uu____3398 = (trie_descend_exact tr included_query)
in (FStar_Util.dflt (trie_empty ()) uu____3398))
in (trie_mutate_leaf tr host_query (fun tr1 uu____3408 -> (mutator tr1 included_trie label))))))


let trie_include : 'a . 'a trie  ->  query  ->  query  ->  'a trie = (fun tr host_query included_query -> (trie_import tr host_query included_query (fun tr1 inc label -> (

let uu___95_3454 = tr1
in {bindings = (ImportedNames (((label), (inc.bindings))))::tr1.bindings; namespaces = uu___95_3454.namespaces}))))


let trie_open_namespace : 'a . 'a trie  ->  query  ->  query  ->  'a trie = (fun tr host_query included_query -> (trie_import tr host_query included_query (fun tr1 inc label -> (

let uu___96_3507 = tr1
in {bindings = uu___96_3507.bindings; namespaces = (ImportedNames (((label), (inc.namespaces))))::tr1.namespaces}))))


let trie_add_alias : 'a . 'a trie  ->  Prims.string  ->  query  ->  query  ->  'a trie = (fun tr key host_query included_query -> (trie_import tr host_query included_query (fun tr1 inc label -> (trie_mutate_leaf tr1 ((key)::[]) (fun _ignored_overwritten_trie uu____3579 -> {bindings = (ImportedNames (((label), (inc.bindings))))::[]; namespaces = []})))))


let names_revmap : 'a 'b . ('a btree  ->  'b)  ->  'a names  ->  (Prims.string Prims.list * 'b) Prims.list = (fun fn name_collections -> (

let rec aux = (fun acc imports name_collections1 -> (FStar_List.fold_left (fun acc1 uu___92_3720 -> (match (uu___92_3720) with
| Names (bt) -> begin
(

let uu____3744 = (

let uu____3752 = (fn bt)
in ((imports), (uu____3752)))
in (uu____3744)::acc1)
end
| ImportedNames (nm, name_collections2) -> begin
(aux acc1 ((nm)::imports) name_collections2)
end)) acc name_collections1))
in (aux [] [] name_collections)))


let btree_find_all : 'a . Prims.string FStar_Pervasives_Native.option  ->  'a btree  ->  (prefix_match * 'a) Prims.list = (fun prefix1 bt -> (btree_fold bt (fun k tr acc -> ((({prefix = prefix1; completion = k}), (tr)))::acc) []))

type name_search_term =
| NSTAll
| NSTNone
| NSTPrefix of Prims.string


let uu___is_NSTAll : name_search_term  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NSTAll -> begin
true
end
| uu____3864 -> begin
false
end))


let uu___is_NSTNone : name_search_term  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NSTNone -> begin
true
end
| uu____3875 -> begin
false
end))


let uu___is_NSTPrefix : name_search_term  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NSTPrefix (_0) -> begin
true
end
| uu____3888 -> begin
false
end))


let __proj__NSTPrefix__item___0 : name_search_term  ->  Prims.string = (fun projectee -> (match (projectee) with
| NSTPrefix (_0) -> begin
_0
end))


let names_find_rev : 'a . 'a names  ->  name_search_term  ->  (path_elem * 'a) Prims.list = (fun names id1 -> (

let matching_values_per_collection_with_imports = (match (id1) with
| NSTNone -> begin
[]
end
| NSTAll -> begin
(names_revmap (btree_find_all FStar_Pervasives_Native.None) names)
end
| NSTPrefix ("") -> begin
(names_revmap (btree_find_all (FStar_Pervasives_Native.Some (""))) names)
end
| NSTPrefix (id2) -> begin
(names_revmap (fun bt -> (btree_find_prefix bt id2)) names)
end)
in (

let matching_values_per_collection = (FStar_List.map (fun uu____4041 -> (match (uu____4041) with
| (imports, matches) -> begin
(FStar_List.map (fun uu____4092 -> (match (uu____4092) with
| (segment, v1) -> begin
(((mk_path_el imports segment)), (v1))
end)) matches)
end)) matching_values_per_collection_with_imports)
in (merge_increasing_lists_rev (fun uu____4110 -> (match (uu____4110) with
| (path_el, uu____4117) -> begin
path_el.segment.completion
end)) matching_values_per_collection))))


let rec trie_find_prefix' : 'a . 'a trie  ->  path  ->  query  ->  (path * 'a) Prims.list  ->  (path * 'a) Prims.list = (fun tr path_acc query acc -> (

let uu____4172 = (match (query) with
| [] -> begin
((NSTAll), (NSTAll), ([]))
end
| (id1)::[] -> begin
((NSTPrefix (id1)), (NSTPrefix (id1)), ([]))
end
| (ns)::query1 -> begin
((NSTPrefix (ns)), (NSTNone), (query1))
end)
in (match (uu____4172) with
| (ns_search_term, bindings_search_term, query1) -> begin
(

let matching_namespaces_rev = (names_find_rev tr.namespaces ns_search_term)
in (

let acc_with_recursive_bindings = (FStar_List.fold_left (fun acc1 uu____4243 -> (match (uu____4243) with
| (path_el, trie) -> begin
(trie_find_prefix' trie ((path_el)::path_acc) query1 acc1)
end)) acc matching_namespaces_rev)
in (

let matching_bindings_rev = (names_find_rev tr.bindings bindings_search_term)
in (FStar_List.rev_map_onto (fun uu____4288 -> (match (uu____4288) with
| (path_el, v1) -> begin
(((FStar_List.rev ((path_el)::path_acc))), (v1))
end)) matching_bindings_rev acc_with_recursive_bindings))))
end)))


let trie_find_prefix : 'a . 'a trie  ->  query  ->  (path * 'a) Prims.list = (fun tr query -> (trie_find_prefix' tr [] query []))

type ns_info =
{ns_name : Prims.string; ns_loaded : Prims.bool}


let __proj__Mkns_info__item__ns_name : ns_info  ->  Prims.string = (fun projectee -> (match (projectee) with
| {ns_name = ns_name; ns_loaded = ns_loaded} -> begin
ns_name
end))


let __proj__Mkns_info__item__ns_loaded : ns_info  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {ns_name = ns_name; ns_loaded = ns_loaded} -> begin
ns_loaded
end))

type mod_info =
{mod_name : Prims.string; mod_path : Prims.string; mod_loaded : Prims.bool}


let __proj__Mkmod_info__item__mod_name : mod_info  ->  Prims.string = (fun projectee -> (match (projectee) with
| {mod_name = mod_name; mod_path = mod_path; mod_loaded = mod_loaded} -> begin
mod_name
end))


let __proj__Mkmod_info__item__mod_path : mod_info  ->  Prims.string = (fun projectee -> (match (projectee) with
| {mod_name = mod_name; mod_path = mod_path; mod_loaded = mod_loaded} -> begin
mod_path
end))


let __proj__Mkmod_info__item__mod_loaded : mod_info  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {mod_name = mod_name; mod_path = mod_path; mod_loaded = mod_loaded} -> begin
mod_loaded
end))


let mod_name : mod_info  ->  Prims.string = (fun md -> md.mod_name)

type mod_symbol =
| Module of mod_info
| Namespace of ns_info


let uu___is_Module : mod_symbol  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Module (_0) -> begin
true
end
| uu____4458 -> begin
false
end))


let __proj__Module__item___0 : mod_symbol  ->  mod_info = (fun projectee -> (match (projectee) with
| Module (_0) -> begin
_0
end))


let uu___is_Namespace : mod_symbol  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Namespace (_0) -> begin
true
end
| uu____4478 -> begin
false
end))


let __proj__Namespace__item___0 : mod_symbol  ->  ns_info = (fun projectee -> (match (projectee) with
| Namespace (_0) -> begin
_0
end))


type lid_symbol =
FStar_Ident.lid

type symbol =
| ModOrNs of mod_symbol
| Lid of lid_symbol


let uu___is_ModOrNs : symbol  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ModOrNs (_0) -> begin
true
end
| uu____4508 -> begin
false
end))


let __proj__ModOrNs__item___0 : symbol  ->  mod_symbol = (fun projectee -> (match (projectee) with
| ModOrNs (_0) -> begin
_0
end))


let uu___is_Lid : symbol  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lid (_0) -> begin
true
end
| uu____4528 -> begin
false
end))


let __proj__Lid__item___0 : symbol  ->  lid_symbol = (fun projectee -> (match (projectee) with
| Lid (_0) -> begin
_0
end))

type table =
{tbl_lids : lid_symbol trie; tbl_mods : mod_symbol trie}


let __proj__Mktable__item__tbl_lids : table  ->  lid_symbol trie = (fun projectee -> (match (projectee) with
| {tbl_lids = tbl_lids; tbl_mods = tbl_mods} -> begin
tbl_lids
end))


let __proj__Mktable__item__tbl_mods : table  ->  mod_symbol trie = (fun projectee -> (match (projectee) with
| {tbl_lids = tbl_lids; tbl_mods = tbl_mods} -> begin
tbl_mods
end))


let empty : table = {tbl_lids = (trie_empty ()); tbl_mods = (trie_empty ())}


let insert : table  ->  query  ->  Prims.string  ->  lid_symbol  ->  table = (fun tbl host_query id1 c -> (

let uu___97_4608 = tbl
in (

let uu____4609 = (trie_insert tbl.tbl_lids host_query id1 c)
in {tbl_lids = uu____4609; tbl_mods = uu___97_4608.tbl_mods})))


let register_alias : table  ->  Prims.string  ->  query  ->  query  ->  table = (fun tbl key host_query included_query -> (

let uu___98_4635 = tbl
in (

let uu____4636 = (trie_add_alias tbl.tbl_lids key host_query included_query)
in {tbl_lids = uu____4636; tbl_mods = uu___98_4635.tbl_mods})))


let register_include : table  ->  query  ->  query  ->  table = (fun tbl host_query included_query -> (

let uu___99_4655 = tbl
in (

let uu____4656 = (trie_include tbl.tbl_lids host_query included_query)
in {tbl_lids = uu____4656; tbl_mods = uu___99_4655.tbl_mods})))


let register_open : table  ->  Prims.bool  ->  query  ->  query  ->  table = (fun tbl is_module host_query included_query -> (match (is_module) with
| true -> begin
(register_include tbl host_query included_query)
end
| uu____4683 -> begin
(

let uu___100_4685 = tbl
in (

let uu____4686 = (trie_open_namespace tbl.tbl_lids host_query included_query)
in {tbl_lids = uu____4686; tbl_mods = uu___100_4685.tbl_mods}))
end))


let register_module_path : table  ->  Prims.bool  ->  Prims.string  ->  query  ->  table = (fun tbl loaded path mod_query -> (

let ins_ns = (fun id1 bindings full_name loaded1 -> (

let uu____4749 = (

let uu____4757 = (names_find_exact bindings id1)
in ((uu____4757), (loaded1)))
in (match (uu____4749) with
| (FStar_Pervasives_Native.None, uu____4767) -> begin
(names_insert bindings id1 (Namespace ({ns_name = full_name; ns_loaded = loaded1})))
end
| (FStar_Pervasives_Native.Some (Namespace ({ns_name = uu____4774; ns_loaded = false})), true) -> begin
(names_insert bindings id1 (Namespace ({ns_name = full_name; ns_loaded = loaded1})))
end
| (FStar_Pervasives_Native.Some (uu____4783), uu____4784) -> begin
bindings
end)))
in (

let ins_mod = (fun id1 bindings full_name loaded1 -> (names_insert bindings id1 (Module ({mod_name = full_name; mod_path = path; mod_loaded = loaded1}))))
in (

let name_of_revq = (fun query -> (FStar_String.concat "." (FStar_List.rev query)))
in (

let ins = (fun id1 q revq bindings loaded1 -> (

let name = (name_of_revq ((id1)::revq))
in (match (q) with
| [] -> begin
(ins_mod id1 bindings name loaded1)
end
| uu____4901 -> begin
(ins_ns id1 bindings name loaded1)
end)))
in (

let uu___101_4908 = tbl
in (

let uu____4909 = (trie_mutate tbl.tbl_mods mod_query [] (fun tr id1 q revq namespaces -> (

let uu___102_4933 = tr
in (

let uu____4936 = (ins id1 q revq tr.bindings loaded)
in {bindings = uu____4936; namespaces = namespaces}))) (fun tr uu____4947 -> tr))
in {tbl_lids = uu___101_4908.tbl_lids; tbl_mods = uu____4909})))))))


let string_of_path : path  ->  Prims.string = (fun path -> (

let uu____4958 = (FStar_List.map (fun el -> el.segment.completion) path)
in (FStar_String.concat "." uu____4958)))


let match_length_of_path : path  ->  Prims.int = (fun path -> (

let uu____4974 = (FStar_List.fold_left (fun acc elem -> (

let uu____5014 = acc
in (match (uu____5014) with
| (acc_len, uu____5036) -> begin
(match (elem.segment.prefix) with
| FStar_Pervasives_Native.Some (prefix1) -> begin
(

let completion_len = (FStar_String.length elem.segment.completion)
in ((((acc_len + (Prims.parse_int "1")) + completion_len)), (((prefix1), (completion_len)))))
end
| FStar_Pervasives_Native.None -> begin
acc
end)
end))) (((Prims.parse_int "0")), (((""), ((Prims.parse_int "0"))))) path)
in (match (uu____4974) with
| (length1, (last_prefix, last_completion_length)) -> begin
(((length1 - (Prims.parse_int "1")) - last_completion_length) + (FStar_String.length last_prefix))
end)))


let first_import_of_path : path  ->  Prims.string FStar_Pervasives_Native.option = (fun path -> (match (path) with
| [] -> begin
FStar_Pervasives_Native.None
end
| ({imports = imports; segment = uu____5122})::uu____5123 -> begin
(FStar_List.last imports)
end))


let alist_of_ns_info : ns_info  ->  (Prims.string * FStar_Util.json) Prims.list = (fun ns_info -> ((("name"), (FStar_Util.JsonStr (ns_info.ns_name))))::((("loaded"), (FStar_Util.JsonBool (ns_info.ns_loaded))))::[])


let alist_of_mod_info : mod_info  ->  (Prims.string * FStar_Util.json) Prims.list = (fun mod_info -> ((("name"), (FStar_Util.JsonStr (mod_info.mod_name))))::((("path"), (FStar_Util.JsonStr (mod_info.mod_path))))::((("loaded"), (FStar_Util.JsonBool (mod_info.mod_loaded))))::[])

type completion_result =
{completion_match_length : Prims.int; completion_candidate : Prims.string; completion_annotation : Prims.string}


let __proj__Mkcompletion_result__item__completion_match_length : completion_result  ->  Prims.int = (fun projectee -> (match (projectee) with
| {completion_match_length = completion_match_length; completion_candidate = completion_candidate; completion_annotation = completion_annotation} -> begin
completion_match_length
end))


let __proj__Mkcompletion_result__item__completion_candidate : completion_result  ->  Prims.string = (fun projectee -> (match (projectee) with
| {completion_match_length = completion_match_length; completion_candidate = completion_candidate; completion_annotation = completion_annotation} -> begin
completion_candidate
end))


let __proj__Mkcompletion_result__item__completion_annotation : completion_result  ->  Prims.string = (fun projectee -> (match (projectee) with
| {completion_match_length = completion_match_length; completion_candidate = completion_candidate; completion_annotation = completion_annotation} -> begin
completion_annotation
end))


let json_of_completion_result : completion_result  ->  FStar_Util.json = (fun result -> FStar_Util.JsonList ((FStar_Util.JsonInt (result.completion_match_length))::(FStar_Util.JsonStr (result.completion_annotation))::(FStar_Util.JsonStr (result.completion_candidate))::[]))


let completion_result_of_lid : 'Auu____5272 . (path * 'Auu____5272)  ->  completion_result = (fun uu____5281 -> (match (uu____5281) with
| (path, _lid) -> begin
(

let uu____5288 = (match_length_of_path path)
in (

let uu____5290 = (string_of_path path)
in (

let uu____5292 = (

let uu____5294 = (first_import_of_path path)
in (FStar_Util.dflt "" uu____5294))
in {completion_match_length = uu____5288; completion_candidate = uu____5290; completion_annotation = uu____5292})))
end))


let completion_result_of_mod : Prims.string  ->  Prims.bool  ->  path  ->  completion_result = (fun annot loaded path -> (

let uu____5320 = (match_length_of_path path)
in (

let uu____5322 = (string_of_path path)
in (

let uu____5324 = (FStar_Util.format1 (match (loaded) with
| true -> begin
" %s "
end
| uu____5329 -> begin
"(%s)"
end) annot)
in {completion_match_length = uu____5320; completion_candidate = uu____5322; completion_annotation = uu____5324}))))


let completion_result_of_ns_or_mod : (path * mod_symbol)  ->  completion_result = (fun uu____5341 -> (match (uu____5341) with
| (path, symb) -> begin
(match (symb) with
| Module ({mod_name = uu____5348; mod_path = uu____5349; mod_loaded = loaded}) -> begin
(completion_result_of_mod "mod" loaded path)
end
| Namespace ({ns_name = uu____5355; ns_loaded = loaded}) -> begin
(completion_result_of_mod "ns" loaded path)
end)
end))


let find_module_or_ns : table  ->  query  ->  mod_symbol FStar_Pervasives_Native.option = (fun tbl query -> (trie_find_exact tbl.tbl_mods query))


let autocomplete_lid : table  ->  query  ->  completion_result Prims.list = (fun tbl query -> (

let uu____5386 = (trie_find_prefix tbl.tbl_lids query)
in (FStar_List.map completion_result_of_lid uu____5386)))


let autocomplete_mod_or_ns : table  ->  query  ->  ((path * mod_symbol)  ->  (path * mod_symbol) FStar_Pervasives_Native.option)  ->  completion_result Prims.list = (fun tbl query filter1 -> (

let uu____5440 = (

let uu____5447 = (trie_find_prefix tbl.tbl_mods query)
in (FStar_All.pipe_right uu____5447 (FStar_List.filter_map filter1)))
in (FStar_All.pipe_right uu____5440 (FStar_List.map completion_result_of_ns_or_mod))))




