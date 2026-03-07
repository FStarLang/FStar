module FStarC.HashMap

(* NOTE: THIS IS A CACHE. COLLISIONS WILL BE DROPPED/OVERWRITTEN.

However you should not get a wrong value from lookup/get as we store the key
in the map too and compare it before returning the value. *)

open FStarC.Effect
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
: ML (hashmap k v)

val remove (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (key : k)
  (m : hashmap k v)
  : ML (hashmap k v)

val lookup (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (key : k)
  (m : hashmap k v)
  : ML (option v)

(* lookup |> Some?.v *)
val get (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (key : k)
  (m : hashmap k v)
  : ML v

val mem (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (key : k)
  (m : hashmap k v)
  : ML bool

val fold (#k #v : _)
  {| deq k |}
  {| hashable k |}
  (f : k -> v -> 'a -> ML 'a)
  (m : hashmap k v)
  (init:'a)
: ML 'a

val cached_fun (#a #b : Type) {| hashable a |} {| deq a |} (f : a -> ML b)
  : ML ((a -> ML b) & (unit -> ML unit))
