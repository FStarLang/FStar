open Prims
type ('key, 'value) t =
  {
  mappings: ('key, 'value) FStar_FunctionalExtensionality.restricted_t }
let __proj__Mkt__item__mappings (projectee : ('key, 'value) t) :
  ('key, 'value) FStar_FunctionalExtensionality.restricted_t=
  match projectee with | { mappings;_} -> mappings
let create (f : 'key -> 'value) : ('key, 'value) t=
  { mappings = (fun x -> f x) }
let sel (m : ('key, 'value) t) (k : 'key) : 'value= m.mappings k
let upd (m : ('key, 'value) t) (k : 'key) (v : 'value) : ('key, 'value) t=
  { mappings = (fun x -> if x = k then v else m.mappings x) }
let restrict (p : unit) (m : ('key, 'value) t) : ('key, 'value) t=
  { mappings = (fun x -> m.mappings x) }
type ('key1, 'value1, 'key2, 'value2, 'k) concat_value = Obj.t
let concat_mappings (m1 : 'key1 -> 'value1) (m2 : 'key2 -> 'value2)
  (k : ('key1, 'key2) FStar_Pervasives.either) : Obj.t=
  match k with
  | FStar_Pervasives.Inl k1 -> Obj.repr (m1 k1)
  | FStar_Pervasives.Inr k2 -> Obj.repr (m2 k2)
let concat (m1 : ('key1, 'value1) t) (m2 : ('key2, 'value2) t) :
  (('key1, 'key2) FStar_Pervasives.either, Obj.t) t=
  { mappings = (fun x -> concat_mappings m1.mappings m2.mappings x) }
type ('key1, 'value1, 'key2, 'ren, 'k) rename_value = 'value1
let rename (m : ('key1, 'value1) t) (key2 : unit) (ren : Obj.t -> 'key1) :
  (Obj.t, ('key1, 'value1, Obj.t, Obj.t, unit) rename_value) t=
  { mappings = (fun x -> m.mappings (ren x)) }
let map (f : 'key -> 'value1 -> 'value2) (m : ('key, 'value1) t) :
  ('key, 'value2) t= { mappings = (fun x -> f x (sel m x)) }
