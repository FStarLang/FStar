open Prims
type ('k, 'v) t =
  ('k, 'v FStar_Pervasives_Native.option)
    FStar_FunctionalExtensionality.restricted_t
let empty (uu___ : unit) : ('uuuuu, 'uuuuu1) t=
  fun x -> FStar_Pervasives_Native.None
let literal (f : 'k -> 'v FStar_Pervasives_Native.option) : ('k, 'v) t=
  fun x -> f x
let sel (m : ('k, 'v) t) (x : 'k) : 'v FStar_Pervasives_Native.option= m x
let upd (m : ('k, 'v) t) (x : 'k) (y : 'v) : ('k, 'v) t=
  fun x1 -> if x1 = x then FStar_Pervasives_Native.Some y else m x1
let remove (m : ('k, 'v) t) (x : 'k) : ('k, 'v) t=
  fun x1 -> if x1 = x then FStar_Pervasives_Native.None else m x1
let contains (m : ('k, 'v) t) (x : 'k) : Prims.bool=
  FStar_Pervasives_Native.uu___is_Some (sel m x)
let const (y : 'v) : ('k, 'v) t=
  literal (fun x -> FStar_Pervasives_Native.Some y)
