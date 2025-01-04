open Prims
type ('key, 'value) t =
  {
  mappings: ('key, 'value) FStar_FunctionalExtensionality.restricted_t ;
  domain: 'key FStar_Set.set }
let __proj__Mkt__item__mappings :
  'key 'value .
    ('key, 'value) t ->
      ('key, 'value) FStar_FunctionalExtensionality.restricted_t
  = fun projectee -> match projectee with | { mappings; domain;_} -> mappings
let __proj__Mkt__item__domain :
  'key 'value . ('key, 'value) t -> 'key FStar_Set.set =
  fun projectee -> match projectee with | { mappings; domain;_} -> domain
let sel : 'key 'value . ('key, 'value) t -> 'key -> 'value =
  fun m -> fun k -> m.mappings k
let upd :
  'key 'value . ('key, 'value) t -> 'key -> 'value -> ('key, 'value) t =
  fun m ->
    fun k ->
      fun v ->
        {
          mappings =
            (FStar_FunctionalExtensionality.on_domain
               (fun x -> if x = k then v else m.mappings x));
          domain = (FStar_Set.union m.domain (FStar_Set.singleton k))
        }
let const : 'key 'value . 'value -> ('key, 'value) t =
  fun v ->
    {
      mappings = (FStar_FunctionalExtensionality.on_domain (fun uu___ -> v));
      domain = (FStar_Set.complement (FStar_Set.empty ()))
    }
let domain : 'key 'value . ('key, 'value) t -> 'key FStar_Set.set =
  fun m -> m.domain
let contains : 'key 'value . ('key, 'value) t -> 'key -> Prims.bool =
  fun m -> fun k -> FStar_Set.mem k m.domain
let concat :
  'key 'value . ('key, 'value) t -> ('key, 'value) t -> ('key, 'value) t =
  fun m1 ->
    fun m2 ->
      {
        mappings =
          (FStar_FunctionalExtensionality.on_domain
             (fun x ->
                if FStar_Set.mem x m2.domain
                then m2.mappings x
                else m1.mappings x));
        domain = (FStar_Set.union m1.domain m2.domain)
      }
let map_val :
  'uuuuu 'uuuuu1 .
    ('uuuuu -> 'uuuuu1) -> unit -> (Obj.t, 'uuuuu) t -> (Obj.t, 'uuuuu1) t
  =
  fun f ->
    fun key ->
      fun m ->
        {
          mappings =
            (FStar_FunctionalExtensionality.on_domain
               (fun x -> f (m.mappings x)));
          domain = (m.domain)
        }
let restrict :
  'key 'value . 'key FStar_Set.set -> ('key, 'value) t -> ('key, 'value) t =
  fun s ->
    fun m ->
      { mappings = (m.mappings); domain = (FStar_Set.intersect s m.domain) }
let const_on : 'key 'value . 'key FStar_Set.set -> 'value -> ('key, 'value) t
  = fun dom -> fun v -> restrict dom (const v)
let map_literal : 'k 'v . ('k -> 'v) -> ('k, 'v) t =
  fun f ->
    {
      mappings = (FStar_FunctionalExtensionality.on_domain f);
      domain = (FStar_Set.complement (FStar_Set.empty ()))
    }
type ('key, 'value, 'm1, 'm2) disjoint_dom = unit
type ('key, 'value, 'm, 'dom) has_dom = unit
type ('key, 'value, 'm1, 'm2) equal = unit