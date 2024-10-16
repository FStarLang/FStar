open Prims
type ('k, 'v) t =
  ('k, 'v FStar_Pervasives_Native.option)
    FStar_FunctionalExtensionality.restricted_t
let empty : 'uuuuu 'uuuuu1 . unit -> ('uuuuu, 'uuuuu1) t =
  fun uu___ ->
    FStar_FunctionalExtensionality.on_domain
      (fun uu___1 -> FStar_Pervasives_Native.None)
let literal : 'k 'v . ('k -> 'v FStar_Pervasives_Native.option) -> ('k, 'v) t
  = fun f -> FStar_FunctionalExtensionality.on_domain (fun x -> f x)
let sel : 'k 'v . ('k, 'v) t -> 'k -> 'v FStar_Pervasives_Native.option =
  fun m -> fun x -> m x
let upd : 'k 'v . ('k, 'v) t -> 'k -> 'v -> ('k, 'v) t =
  fun m ->
    fun x ->
      fun y ->
        FStar_FunctionalExtensionality.on_domain
          (fun x1 -> if x1 = x then FStar_Pervasives_Native.Some y else m x1)
let remove : 'k 'v . ('k, 'v) t -> 'k -> ('k, 'v) t =
  fun m ->
    fun x ->
      FStar_FunctionalExtensionality.on_domain
        (fun x1 -> if x1 = x then FStar_Pervasives_Native.None else m x1)
let contains : 'k 'v . ('k, 'v) t -> 'k -> Prims.bool =
  fun m -> fun x -> FStar_Pervasives_Native.uu___is_Some (sel m x)
let const : 'k 'v . 'v -> ('k, 'v) t =
  fun y -> literal (fun x -> FStar_Pervasives_Native.Some y)
type ('k, 'v, 'm1, 'm2) equal = unit