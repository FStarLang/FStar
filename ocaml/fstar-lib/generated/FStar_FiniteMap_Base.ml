open Prims
type ('a, 'b, 's) setfun_t =
  ('a, 'b FStar_Pervasives_Native.option)
    FStar_FunctionalExtensionality.restricted_t
type ('a, 'b) map =
  ('a FStar_FiniteSet_Base.set, ('a, 'b, unit) setfun_t) Prims.dtuple2
let domain : 'a 'b . ('a, 'b) map -> 'a FStar_FiniteSet_Base.set =
  fun m ->
    let uu___ = m in
    match uu___ with | Prims.Mkdtuple2 (keys, uu___1) -> keys
let elements : 'a 'b . ('a, 'b) map -> ('a, 'b, unit) setfun_t =
  fun m ->
    let uu___ = m in match uu___ with | Prims.Mkdtuple2 (uu___1, f) -> f
let mem : 'a 'b . 'a -> ('a, 'b) map -> Prims.bool =
  fun key -> fun m -> FStar_FiniteSet_Base.mem key (domain m)
let rec key_in_item_list : 'a 'b . 'a -> ('a * 'b) Prims.list -> Prims.bool =
  fun key ->
    fun items ->
      match items with
      | [] -> false
      | (k, v)::tl -> (key = k) || (key_in_item_list key tl)
let rec item_list_doesnt_repeat_keys :
  'a 'b . ('a * 'b) Prims.list -> Prims.bool =
  fun items ->
    match items with
    | [] -> true
    | (k, v)::tl ->
        (Prims.op_Negation (key_in_item_list k tl)) &&
          (item_list_doesnt_repeat_keys tl)
let lookup : 'a 'b . 'a -> ('a, 'b) map -> 'b =
  fun key ->
    fun m -> FStar_Pervasives_Native.__proj__Some__item__v (elements m key)
type ('a, 'b, 'm) values = unit
type ('a, 'b, 'm) items = unit
let emptymap : 'a 'b . unit -> ('a, 'b) map =
  fun uu___ ->
    Prims.Mkdtuple2
      ((FStar_FiniteSet_Base.emptyset ()),
        (FStar_FunctionalExtensionality.on_domain
           (fun key -> FStar_Pervasives_Native.None)))
let glue :
  'a 'b .
    'a FStar_FiniteSet_Base.set -> ('a, 'b, unit) setfun_t -> ('a, 'b) map
  = fun keys -> fun f -> Prims.Mkdtuple2 (keys, f)
let insert : 'a 'b . 'a -> 'b -> ('a, 'b) map -> ('a, 'b) map =
  fun k ->
    fun v ->
      fun m ->
        let keys' = FStar_FiniteSet_Base.insert k (domain m) in
        let f' =
          FStar_FunctionalExtensionality.on_domain
            (fun key ->
               if key = k
               then FStar_Pervasives_Native.Some v
               else elements m key) in
        Prims.Mkdtuple2 (keys', f')
let merge : 'a 'b . ('a, 'b) map -> ('a, 'b) map -> ('a, 'b) map =
  fun m1 ->
    fun m2 ->
      let keys' = FStar_FiniteSet_Base.union (domain m1) (domain m2) in
      let f' =
        FStar_FunctionalExtensionality.on_domain
          (fun key ->
             if FStar_FiniteSet_Base.mem key (domain m2)
             then elements m2 key
             else elements m1 key) in
      Prims.Mkdtuple2 (keys', f')
let subtract :
  'a 'b . ('a, 'b) map -> 'a FStar_FiniteSet_Base.set -> ('a, 'b) map =
  fun m ->
    fun s ->
      let keys' = FStar_FiniteSet_Base.difference (domain m) s in
      let f' =
        FStar_FunctionalExtensionality.on_domain
          (fun key ->
             if FStar_FiniteSet_Base.mem key keys'
             then elements m key
             else FStar_Pervasives_Native.None) in
      Prims.Mkdtuple2 (keys', f')
type ('a, 'b, 'm1, 'm2) equal = unit
type ('a, 'b, 'm1, 'm2) disjoint = unit
let remove : 'a 'b . 'a -> ('a, 'b) map -> ('a, 'b) map =
  fun key -> fun m -> subtract m (FStar_FiniteSet_Base.singleton key)
let notin : 'a 'b . 'a -> ('a, 'b) map -> Prims.bool =
  fun key -> fun m -> Prims.op_Negation (mem key m)
type cardinality_zero_iff_empty_fact = unit
type empty_or_domain_occupied_fact = unit
type empty_or_values_occupied_fact = unit
type empty_or_items_occupied_fact = unit
type map_cardinality_matches_domain_fact = unit
type values_contains_fact = unit
type items_contains_fact = unit
type empty_domain_empty_fact = unit
type glue_domain_fact = unit
type glue_elements_fact = unit
type insert_elements_fact = unit
type insert_member_cardinality_fact = unit
type insert_nonmember_cardinality_fact = unit
type merge_domain_is_union_fact = unit
type merge_element_fact = unit
type subtract_domain_fact = unit
type subtract_element_fact = unit
type map_equal_fact = unit
type map_extensionality_fact = unit
type disjoint_fact = unit
type all_finite_map_facts = unit