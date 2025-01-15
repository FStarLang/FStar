module FStarC.HashMap

(* NOTE: THIS IS A CACHE. COLLISIONS WILL BE DROPPED/OVERWRITTEN.

However you should not get a wrong value from lookup/get as we store the key
in the map too and compare it before returning the value. *)

open FStarC.Class.Deq
open FStarC.Class.Hashable

val hashmap (k v : Type) : Type0

type t = hashmap

val empty (#k #v : _) : hashmap k v

val add (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (key : k)
  (value : v)
  (m : hashmap k v)
: hashmap k v

val remove (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (key : k)
  (m : hashmap k v)
  : hashmap k v

val lookup (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (key : k)
  (m : hashmap k v)
  : option v

(* lookup |> Some?.v *)
val get (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (key : k)
  (m : hashmap k v)
  : v

val mem (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (key : k)
  (m : hashmap k v)
  : bool

val cached_fun (#a #b : Type) {| hashable a |} {| deq a |} (f : a -> b)
  : (a -> b) & (unit -> unit) // along with a reset fun
