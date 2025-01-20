open Prims
type ('a, 'f) total_order = unit
type 'a cmp = 'a -> 'a -> Prims.bool
type ('k, 'v, 'f, 'd) map_t =
  ('k, 'v FStar_Pervasives_Native.option)
    FStar_FunctionalExtensionality.restricted_t
type ('k, 'v, 'f) ordmap =
  | Mk_map of ('k, unit) FStar_OrdSet.ordset * ('k, 'v, unit, unit) map_t 
let uu___is_Mk_map :
  'k 'v . 'k FStar_OrdSet.cmp -> ('k, 'v, unit) ordmap -> Prims.bool =
  fun f -> fun projectee -> true
let __proj__Mk_map__item__d :
  'k 'v .
    'k FStar_OrdSet.cmp ->
      ('k, 'v, unit) ordmap -> ('k, unit) FStar_OrdSet.ordset
  = fun f -> fun projectee -> match projectee with | Mk_map (d, m) -> d
let __proj__Mk_map__item__m :
  'k 'v .
    'k FStar_OrdSet.cmp ->
      ('k, 'v, unit) ordmap -> ('k, 'v, unit, unit) map_t
  = fun f -> fun projectee -> match projectee with | Mk_map (d, m) -> m
let empty : 'k 'v . 'k FStar_OrdSet.cmp -> ('k, 'v, unit) ordmap =
  fun f ->
    let d = FStar_OrdSet.empty f in
    let g =
      FStar_FunctionalExtensionality.on_domain
        (fun x -> FStar_Pervasives_Native.None) in
    Mk_map (d, g)
let const_on :
  'k 'v .
    'k FStar_OrdSet.cmp ->
      ('k, unit) FStar_OrdSet.ordset -> 'v -> ('k, 'v, unit) ordmap
  =
  fun f ->
    fun d ->
      fun x ->
        let g =
          FStar_FunctionalExtensionality.on_domain
            (fun y ->
               if FStar_OrdSet.mem f y d
               then FStar_Pervasives_Native.Some x
               else FStar_Pervasives_Native.None) in
        Mk_map (d, g)
let select :
  'k 'v .
    'k FStar_OrdSet.cmp ->
      'k -> ('k, 'v, unit) ordmap -> 'v FStar_Pervasives_Native.option
  = fun f -> fun x -> fun m -> __proj__Mk_map__item__m f m x
let insert :
  'a .
    'a FStar_OrdSet.cmp ->
      'a -> ('a, unit) FStar_OrdSet.ordset -> ('a, unit) FStar_OrdSet.ordset
  =
  fun f ->
    fun x -> fun s -> FStar_OrdSet.union f (FStar_OrdSet.singleton f x) s
let update :
  'k 'v .
    'k FStar_OrdSet.cmp ->
      'k -> 'v -> ('k, 'v, unit) ordmap -> ('k, 'v, unit) ordmap
  =
  fun f ->
    fun x ->
      fun y ->
        fun m ->
          let s' = insert f x (__proj__Mk_map__item__d f m) in
          let g' =
            FStar_FunctionalExtensionality.on_domain
              (fun x' ->
                 if x' = x
                 then FStar_Pervasives_Native.Some y
                 else __proj__Mk_map__item__m f m x') in
          Mk_map (s', g')
let contains :
  'k 'v . 'k FStar_OrdSet.cmp -> 'k -> ('k, 'v, unit) ordmap -> Prims.bool =
  fun f ->
    fun x -> fun m -> FStar_OrdSet.mem f x (__proj__Mk_map__item__d f m)
let dom :
  'k 'v .
    'k FStar_OrdSet.cmp ->
      ('k, 'v, unit) ordmap -> ('k, unit) FStar_OrdSet.ordset
  = fun f -> fun m -> __proj__Mk_map__item__d f m
let remove :
  'k 'v .
    'k FStar_OrdSet.cmp ->
      'k -> ('k, 'v, unit) ordmap -> ('k, 'v, unit) ordmap
  =
  fun f ->
    fun x ->
      fun m ->
        let s' = FStar_OrdSet.remove f x (__proj__Mk_map__item__d f m) in
        let g' =
          FStar_FunctionalExtensionality.on_domain
            (fun x' ->
               if x' = x
               then FStar_Pervasives_Native.None
               else __proj__Mk_map__item__m f m x') in
        Mk_map (s', g')
let choose :
  'k 'v .
    'k FStar_OrdSet.cmp ->
      ('k, 'v, unit) ordmap -> ('k * 'v) FStar_Pervasives_Native.option
  =
  fun f ->
    fun m ->
      match FStar_OrdSet.choose f (__proj__Mk_map__item__d f m) with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some x ->
          FStar_Pervasives_Native.Some
            (x,
              (FStar_Pervasives_Native.__proj__Some__item__v
                 (__proj__Mk_map__item__m f m x)))
let size : 'k 'v . 'k FStar_OrdSet.cmp -> ('k, 'v, unit) ordmap -> Prims.nat
  = fun f -> fun m -> FStar_OrdSet.size f (__proj__Mk_map__item__d f m)
type ('k, 'v, 'f, 'm1, 'm2) equal = unit