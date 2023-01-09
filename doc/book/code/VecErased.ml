open Prims
type ('a, 'dummyV0) vec =
  | Nil 
  | Cons of unit * 'a * ('a, unit) vec 
let uu___is_Nil : 'a . Prims.nat -> ('a, unit) vec -> Prims.bool =
  fun uu___ ->
    fun projectee -> match projectee with | Nil -> true | uu___1 -> false
let uu___is_Cons : 'a . Prims.nat -> ('a, unit) vec -> Prims.bool =
  fun uu___ ->
    fun projectee ->
      match projectee with | Cons (n, hd, tl) -> true | uu___1 -> false
let __proj__Cons__item__hd : 'a . Prims.nat -> ('a, unit) vec -> 'a =
  fun uu___ -> fun projectee -> match projectee with | Cons (n, hd, tl) -> hd
let __proj__Cons__item__tl :
  'a . Prims.nat -> ('a, unit) vec -> ('a, unit) vec =
  fun uu___ -> fun projectee -> match projectee with | Cons (n, hd, tl) -> tl
let rec append :
  'a . unit -> unit -> ('a, unit) vec -> ('a, unit) vec -> ('a, unit) vec =
  fun n ->
    fun m ->
      fun v0 ->
        fun v1 ->
          match v0 with
          | Nil -> v1
          | Cons (uu___, hd, tl) -> Cons ((), hd, (append () () tl v1))