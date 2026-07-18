open Prims
type 'a cmp = 'a -> 'a -> Prims.bool
type ('k, 'v, 'f, 'd) map_t =
  ('k, 'v FStar_Pervasives_Native.option)
    FStar_FunctionalExtensionality.restricted_t
type ('k, 'v, 'f) ordmap =
  | Mk_map of ('k, 'f) FStar_OrdSet.ordset * ('k, 'v, 'f, Obj.t) map_t 
let uu___is_Mk_map (f : 'k FStar_OrdSet.cmp)
  (projectee : ('k, 'v, Obj.t) ordmap) : Prims.bool= true
let __proj__Mk_map__item__d (f : 'k FStar_OrdSet.cmp)
  (projectee : ('k, 'v, Obj.t) ordmap) : ('k, Obj.t) FStar_OrdSet.ordset=
  match projectee with | Mk_map (d, m) -> d
let __proj__Mk_map__item__m (f : 'k FStar_OrdSet.cmp)
  (projectee : ('k, 'v, Obj.t) ordmap) : ('k, 'v, Obj.t, Obj.t) map_t=
  match projectee with | Mk_map (d, m) -> m
let empty (f : 'k FStar_OrdSet.cmp) : ('k, 'v, Obj.t) ordmap=
  let d = FStar_OrdSet.empty f in
  let g x = FStar_Pervasives_Native.None in Mk_map (d, g)
let const_on (f : 'k FStar_OrdSet.cmp) (d : ('k, Obj.t) FStar_OrdSet.ordset)
  (x : 'v) : ('k, 'v, Obj.t) ordmap=
  let g x1 =
    if FStar_OrdSet.mem f x1 d
    then FStar_Pervasives_Native.Some x
    else FStar_Pervasives_Native.None in
  Mk_map (d, g)
let select (f : 'k FStar_OrdSet.cmp) (x : 'k) (m : ('k, 'v, Obj.t) ordmap) :
  'v FStar_Pervasives_Native.option= __proj__Mk_map__item__m f m x
let insert (f : 'a FStar_OrdSet.cmp) (x : 'a)
  (s : ('a, Obj.t) FStar_OrdSet.ordset) : ('a, Obj.t) FStar_OrdSet.ordset=
  FStar_OrdSet.union f (FStar_OrdSet.singleton f x) s
let update (f : 'k FStar_OrdSet.cmp) (x : 'k) (y : 'v)
  (m : ('k, 'v, Obj.t) ordmap) : ('k, 'v, Obj.t) ordmap=
  let s' = insert f x (__proj__Mk_map__item__d f m) in
  let g' x1 =
    if x1 = x
    then FStar_Pervasives_Native.Some y
    else __proj__Mk_map__item__m f m x1 in
  Mk_map (s', g')
let contains (f : 'k FStar_OrdSet.cmp) (x : 'k) (m : ('k, 'v, Obj.t) ordmap)
  : Prims.bool= FStar_OrdSet.mem f x (__proj__Mk_map__item__d f m)
let dom (f : 'k FStar_OrdSet.cmp) (m : ('k, 'v, Obj.t) ordmap) :
  ('k, Obj.t) FStar_OrdSet.ordset= __proj__Mk_map__item__d f m
let remove (f : 'k FStar_OrdSet.cmp) (x : 'k) (m : ('k, 'v, Obj.t) ordmap) :
  ('k, 'v, Obj.t) ordmap=
  let s' = FStar_OrdSet.remove f x (__proj__Mk_map__item__d f m) in
  let g' x1 =
    if x1 = x
    then FStar_Pervasives_Native.None
    else __proj__Mk_map__item__m f m x1 in
  Mk_map (s', g')
let choose (f : 'k FStar_OrdSet.cmp) (m : ('k, 'v, Obj.t) ordmap) :
  ('k * 'v) FStar_Pervasives_Native.option=
  match FStar_OrdSet.choose f (__proj__Mk_map__item__d f m) with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some x ->
      FStar_Pervasives_Native.Some
        (x,
          (FStar_Pervasives_Native.__proj__Some__item__v
             (__proj__Mk_map__item__m f m x)))
let size (f : 'k FStar_OrdSet.cmp) (m : ('k, 'v, Obj.t) ordmap) : Prims.nat=
  FStar_OrdSet.size f (__proj__Mk_map__item__d f m)
