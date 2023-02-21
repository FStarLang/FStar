open Prims
type ('key, 'value) t =
  {
  mappings: ('key, 'value) FStar_FunctionalExtensionality.restricted_t }
let __proj__Mkt__item__mappings :
  'key 'value .
    ('key, 'value) t ->
      ('key, 'value) FStar_FunctionalExtensionality.restricted_t
  = fun projectee -> match projectee with | { mappings;_} -> mappings
let create : 'key 'value . ('key -> 'value) -> ('key, 'value) t =
  fun f -> { mappings = (FStar_FunctionalExtensionality.on_domain f) }
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
               (fun k' -> if k' = k then v else m.mappings k'))
        }
type ('key, 'value, 'm1, 'm2) equal = unit
let restrict : 'key 'value 'p . ('key, 'value) t -> ('key, 'value) t =
  fun m ->
    { mappings = (FStar_FunctionalExtensionality.on_domain m.mappings) }
type ('key1, 'value1, 'key2, 'value2, 'k) concat_value = Obj.t
let concat_mappings :
  'key1 'value1 'key2 'value2 .
    ('key1 -> 'value1) ->
      ('key2 -> 'value2) -> ('key1, 'key2) FStar_Pervasives.either -> Obj.t
  =
  fun m1 ->
    fun m2 ->
      fun k ->
        match k with
        | FStar_Pervasives.Inl k1 -> Obj.repr (m1 k1)
        | FStar_Pervasives.Inr k2 -> Obj.repr (m2 k2)
let concat :
  'key1 'value1 'key2 'value2 .
    ('key1, 'value1) t ->
      ('key2, 'value2) t -> (('key1, 'key2) FStar_Pervasives.either, Obj.t) t
  =
  fun m1 ->
    fun m2 ->
      {
        mappings =
          (FStar_FunctionalExtensionality.on_domain
             (concat_mappings m1.mappings m2.mappings))
      }
type ('key1, 'value1, 'key2, 'ren, 'k) rename_value = 'value1
let rename :
  'key1 'value1 .
    ('key1, 'value1) t ->
      unit ->
        (Obj.t -> 'key1) ->
          (Obj.t, ('key1, 'value1, Obj.t, unit, unit) rename_value) t
  =
  fun m ->
    fun key2 ->
      fun ren ->
        {
          mappings =
            (FStar_FunctionalExtensionality.on_domain
               (fun k2 -> m.mappings (ren k2)))
        }
let map :
  'key 'value1 'value2 .
    ('key -> 'value1 -> 'value2) -> ('key, 'value1) t -> ('key, 'value2) t
  =
  fun f ->
    fun m ->
      {
        mappings =
          (FStar_FunctionalExtensionality.on_domain (fun k -> f k (sel m k)))
      }